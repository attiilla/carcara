//Question: outer_premises that aren't resolution can be thrown out after cloning their data to the parts?
//Only steps that are resolution and are premise of another resolution are compressed by lower units

mod tracker;
mod disjoints;
mod error;
use crate::compressor::error::*;
use crate::ast::proof::*;
//use crate::ast::node::*;
use std::collections::{HashSet, HashMap};
//use std::ops::Index;
//use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution/*, unremove_all_negations*/};
use crate::checker::error::CheckerError;
use crate::ast::rc::Rc;
use indexmap::IndexSet;
use std::env;
//use std::env;
use tracker::*;
//use disjoints::*;

//WARNING: Ignore contractions

fn print_proof(p: &Vec<ProofCommand>, indentation: String, base: usize) -> usize{
    let mut from = base;
    let mut sub_len: usize = 0;
    for (i, c) in p.iter().enumerate(){
        match c{
            ProofCommand::Assume { id, term } => println!("{}{} - {} Assume: {}", &indentation, i+from, id, term),
            ProofCommand::Step(ps) => {
                let mut s: String = format!("{}{} - {} {}: {:?}", &indentation, from+i, &ps.id, &ps.rule, &ps.clause).to_string();
                if ps.premises.len()>0{
                    let prem = format!(", premises: {:?}", &ps.premises);
                    s = s + &prem;
                }
                if ps.args.len()>0{
                    let args = format!(", args: {:?}", &ps.premises);
                    s = s + &args;
                }
                if ps.discharge.len()>0{
                    let disc = format!(", discharge: {:?}", &ps.discharge);
                    s = s + &disc;
                }
                println!("{}",s);
            }
            ProofCommand::Subproof(sp) => {
                let new_indentation = indentation.clone() + "   ";
                //println!("i: {i}, from: {from}");
                sub_len = print_proof(&sp.commands, new_indentation, i+from);
                from += sub_len;
            }
        }
    }
    p.len()+sub_len-1
}

#[derive(Debug)]
pub struct ProofCompressor{
    proof: Proof,
}

//sp_binder: HashSet<&'static str>,
//sp_binder: HashSet::from_iter(vec!["subproof","let","sko_ex","sko_forall","bind","onepoint"].into_iter()),

impl ProofCompressor{
    pub fn from(p: Proof)->Self{
        Self{
            proof: p,
        }
    }

    /*pub fn compress_proof(&mut self) -> Proof{
        let empty = vec![];
        self.lower_units(empty);
        self.proof.clone()
    }

    fn lower_units(&mut self, sub_adrs: Vec<usize>) -> Result<(),()>{
        self.collect_units(&sub_adrs);
        //self.fix_broken_proof();
        //self.reinsert_units();
        //self.rebuild();
        Ok(())
    }*/

    pub fn compress_proof(&mut self) -> Proof{
        env::set_var("RUST_BACKTRACE", "1");
        print_proof(&self.proof.commands, "".to_string(), 0);
        let _ = self.lower_units(vec![], 0);
        self.proof.clone()
    }

    fn lower_units(&mut self, sub_adrs: Vec<usize>, debug_aux: usize) -> Result<IndexSet<(usize,usize)>, ()> {
        let (pt, premises_from_sub) = self.collect_units(&sub_adrs, debug_aux);
        Ok(premises_from_sub)
    }

    fn collect_units(&mut self, sub_adrs: &Vec<usize>, debug_aux: usize) -> (PartTracker, IndexSet<(usize,usize)>){
        println!("Diving into subproofs from level {debug_aux}");
        let (subproof_to_outer_premises, mut outer_premises)= self.process_subproofs(sub_adrs, debug_aux+1);
        let depth: usize = sub_adrs.len();
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        //let m_commands: &mut Vec<ProofCommand> = ;
        let n = commands.len();
        let mut pt = PartTracker::new(self.step_is_resolution((depth,n-1), sub_adrs), sub_adrs.len());
        pt.add_step_to_part((depth,n-1),1); //adds conclusion to part 1
        pt.set_is_conclusion((depth,n-1));
        println!("Collecting units on level {debug_aux}");
        let _ = if debug_aux==1 {print_proof(commands, "".to_string(), 0)} else {0};
        for (i, c) in commands.iter().enumerate().rev(){
            match c{
                ProofCommand::Assume{id, term} => {
                    if debug_aux==1 {println!("id: {:?}", id)};

                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    pt.add_step_to_part((depth,i), 0); //all assumes must be in the part 0
                    match pt.parts_containing((depth,i)){
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => 
                            panic!("This error should be impossible in this part of the code.\nThis node was added to part 0 just some lines above"),
                        Err(_) => panic!("Unexpected error"),
                    }

                    for &containing_part in &containing{
                        // Check if this step must be collected in this part
                        if pt.is_premise_of_resolution((depth,i)) &&
                        pt.counting_in_part((depth,i), containing_part)>=2 &&
                        pt.is_resolution_part(containing_part)
                        {
                            pt.add_to_units_queue_of_part((depth,i),containing_part);
                        }
                        // Now the data in the Assume should be added to the DisjointParts of the Tracker
                        pt.clone_data_to_part((depth,i),containing_part, commands, None);
                    }
                }

                ProofCommand::Step(ps) => {
                    if debug_aux==1 {println!("id: {:?}", &ps.id)};


                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    match pt.parts_containing((depth,i)){
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => {
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i),self.step_is_resolution((depth,i), sub_adrs));
                            containing.push(new_part_ind);
                        }
                        Err(_) => panic!("Unexpected error"),
                    }
                    
                    // Case 1
                    // If this node is a resolution, every premise is in the same parts
                    if ps.rule == "resolution" || ps.rule == "th-resolution" {
                        // First we check if this is one of the steps that can't be deleted
                        // If it isn't conclusion of a part and can't be deleted, we create a 
                        // new part with this step as conclusion
                        if pt.must_be_a_new_conclusion((depth,i)){
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i), true);
                            containing.push(new_part_ind);
                        }
                        for &containing_part in &containing{
                            for &prem in &ps.premises{
                                pt.add_step_to_part(prem, containing_part);
                                if prem.0!=depth{ // mark premises from other command vectors
                                    outer_premises.insert(prem);
                                }
                                pt.set_resolutions_premise(prem); // marks this premise as premise of a resolution
                            }

                            // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                            pt.clone_data_to_part((depth,i),containing_part, commands, None);

                            // Check if this step must be collected in this part
                            if pt.counting_in_part((depth,i), containing_part)>=2 && self.get_clause_len((depth,i), sub_adrs)==1{
                                pt.add_to_units_queue_of_part((depth,i),containing_part);
                            }
                        }
                    }

                    // Case 2
                    // If this node is not a resolution but is premise of a resolution,
                    // it will be in the same parts as the resolutions who use it, but its
                    // premises will be in their own parts if they are resolutions
                    // non-resolution premises will be in a single non-resolution part
                    else if pt.is_premise_of_resolution((depth,i)){
                        let mut premise_not_r: Vec<(usize,usize)> = vec![];
                        for &prem in &ps.premises{
                            if self.step_is_resolution(prem, sub_adrs){
                                pt.add_step_to_new_part((depth,i), true); // creates new parts for the premises that are resolutions
                            } else {
                                premise_not_r.push(prem); // stores the premises that aren't resolutions
                            }
                            if prem.0!=depth{ // mark premises from other command vectors
                                outer_premises.insert(prem);
                            }
                        }

                        // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
                        // or create a single part for this node and all it's non-resolution premises
                        if premise_not_r.len()>0{ // checks if there is a non-resolution premise
                            let non_resolution_parts = pt.non_resolution_parts((depth,i));
                            if non_resolution_parts.len()==0{ // checks if every part of this step is a resolution part, so we will create a new part
                                let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                                containing.push(new_part_ind);
                                for &prem in &premise_not_r{
                                    pt.add_step_to_part(prem, new_part_ind)
                                }
                            } else {
                                for containing_part in non_resolution_parts{
                                    for &prem in &premise_not_r{
                                        pt.add_step_to_part(prem, containing_part)
                                    }
                                }
                            }
                        }
                        // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                        for &containing_part in &containing{    
                            pt.clone_data_to_part((depth,i),containing_part, commands, None);
                        }
                    }

                    // Case 3
                    // If the node is not a resolution nor premise of one
                    else {
                        for &prem in &ps.premises{
                            // If the premise is a resolution, it will be the conclusion of a new part
                            if self.get_rule(prem, sub_adrs) == "resolution" || self.get_rule(prem, sub_adrs) == "th-resolution"{
                                if prem.0!=depth{
                                    outer_premises.insert(prem);
                                } else {
                                    pt.add_step_to_new_part(prem,true);
                                }
                            } 
                            // If the premise is not a resolution, just add it to the parts containing the current step 
                            else {
                                for &containing_part in &containing{
                                    pt.add_step_to_part(prem, containing_part);
                                    if prem.0!=depth{
                                        outer_premises.insert(prem);
                                    }
                                }
                            }
                        }
                        for &containing_part in &containing{
                            // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                            pt.clone_data_to_part((depth,i),containing_part, commands, None);
                        }
                    }
                }
                
                ProofCommand::Subproof(sp) => {
                    // At first, recursivelly call lower units on the subproof
                    // it should return every premise used by the subproof that is outside of the subproof
                    /*let mut new_subproof_adrs = sub_adrs.clone();
                    new_subproof_adrs.push(i);
                    let sp_result: Result<IndexSet<(usize,usize)>,_> = self.lower_units(new_subproof_adrs);*/
                    let sp_premises: Vec<(usize,usize)>;
                    match subproof_to_outer_premises.get(&i){
                        Some(v) => sp_premises = v.iter().cloned().collect(),
                        None => panic!("No outer premises. Add an empty set to the structure if a subproof has no outer premise")
                    };
                    let same_depth_premises: Vec<(usize,usize)> = sp_premises.iter().filter( |&&x | x.0==depth).cloned().collect();
                    let other_depth_premises: Vec<(usize,usize)> = sp_premises.iter().filter( |&&x | x.0<depth).cloned().collect();
                    outer_premises.extend(other_depth_premises);

                    
                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    match pt.parts_containing((depth,i)){//WARNING
                    //CORNER CASE TO TEST: Node is a subproof that isn't used as premise for any node of same depth
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => {
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                            containing.push(new_part_ind);
                        }
                        Err(_) => panic!("Unexpected error"),
                    }
                    
                    //Get the premises of the last step of the subproof and extend with hidden premises of same depth
                    let mut last_step_premises: IndexSet<(usize,usize)> = IndexSet::new();
                    match self.get_premises((depth,i), sub_adrs){
                        Some(v) => { //CHECK
                            let vv = v.clone();
                            last_step_premises.extend(vv.iter())
                        }
                        None => ()
                    }
                    let mut last_step_and_same_depth_premises: IndexSet<(usize,usize)> = last_step_premises.clone();
                    last_step_and_same_depth_premises.extend(same_depth_premises.iter());

                    // If the subproof is not premise of a resolution, it's resolution premises of same depth will be conclusion of new parts
                    // and it's other premises will be added to it's parts
                    if !pt.is_premise_of_resolution((depth,i)){
                        for &prem in &last_step_and_same_depth_premises{
                            if self.step_is_resolution(prem, sub_adrs) && prem.0==depth{
                                pt.add_step_to_new_part(prem, true);
                            } else {
                                for &containing_parts in &containing {
                                    pt.add_step_to_part(prem, containing_parts);
                                }
                            }
                        }
                    }
                    // In the other scenario, a heavy logic much like the Case 2 of ProofStep will be used
                    else{
                        let mut premise_not_r_of_same_depth: Vec<(usize,usize)> = vec![];
                        for &prem in &last_step_and_same_depth_premises{
                            if self.step_is_resolution(prem, sub_adrs) && prem.0==depth{
                                pt.add_step_to_new_part((depth,i), true); // creates new parts for the premises that are resolutions of same depth
                            } else {
                                premise_not_r_of_same_depth.push(prem); // stores the premises that aren't resolutions
                            }
                        }
                        if premise_not_r_of_same_depth.len()>0{ // checks if there is a non-resolution premise
                            let non_resolution_parts = pt.non_resolution_parts((depth,i));
                            if non_resolution_parts.len()==0{ // checks if every part of this step is a resolution part, so we will create a new part
                                let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                                containing.push(new_part_ind);
                                for prem in premise_not_r_of_same_depth{
                                    pt.add_step_to_part(prem, new_part_ind)
                                }
                            } else {
                                for &containing_part in &non_resolution_parts{
                                    for &prem in &premise_not_r_of_same_depth{
                                        pt.add_step_to_part(prem, containing_part)
                                    }
                                }
                            }
                        }
                    }

                    // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                    for &containing_part in &containing{    
                        pt.clone_data_to_part((depth,i),containing_part, commands, Some(sp_premises.clone()));
                    }

                    // And now the steps that can't be deleted are marked
                    for needed in same_depth_premises{
                        if self.step_is_resolution(needed, sub_adrs){
                            pt.set_cant_be_deleted(needed);
                        }
                    }

                }
            };
        }
        // Now we will clone the data from outer premises in the respective parts
        // WARNING: After debugging this entire loop might be deleted
        for &outer_step in outer_premises.iter(){
            let mut containing: Vec<usize> = vec![];
            match pt.parts_containing(outer_step){
                Ok(v) => containing = v,
                Err(_) => panic!("There is an error in the logic. You added this step to outer_premises without adding it to its respective parts."),
            }
            let outer_commands: &Vec<ProofCommand> = self.dive_into_proof(&sub_adrs[0..outer_step.0]);
            for containing_part in containing{
                pt.clone_data_to_part(outer_step, containing_part, outer_commands, Some(vec![]));
            }
        }

        (pt,outer_premises)
    }

    fn process_subproofs(&mut self, sub_adrs: &Vec<usize>, debug_aux: usize) -> (HashMap<usize,IndexSet<(usize,usize)>>, IndexSet<(usize,usize)>){
        println!("Processing subproofs on level {debug_aux}");
        let mut all_outer_premises: IndexSet<(usize,usize)> = IndexSet::new();
        let mut subproofs_to_outer_premises: HashMap<usize,IndexSet<(usize,usize)>> = HashMap::new();
        let mut subproofs_ind: Vec<usize> = Vec::new();
        let commands = self.dive_into_proof(sub_adrs);
        for (i, c) in commands.iter().enumerate(){
            match c{
                ProofCommand::Subproof(_) => subproofs_ind.push(i),
                _ => ()
            }
        }
        for i in subproofs_ind{
            let m_commands = self.dive_into_proof_mut(sub_adrs);
            if let ProofCommand::Subproof(sp) = &mut m_commands[i]{
                let mut new_sub_adrs = sub_adrs.clone();
                new_sub_adrs.push(i);
                println!("Diving in subproof {i} of depth {debug_aux}");
                let sp_result = self.lower_units(new_sub_adrs, debug_aux);
                println!("Emerging from subproof {i} of depth {debug_aux}");
                match sp_result{
                    Ok(sp_premises) => {
                        all_outer_premises.extend(sp_premises.iter());
                        subproofs_to_outer_premises.insert(i, sp_premises);
                    },
                    Err(_) => panic!("Some subproof coudn't be compressed")
                }
            }else{
                panic!("AAAAAAAAAAAARRRGHH, CURSE YOU BAYLE!!!!")
            }
        }
        (subproofs_to_outer_premises, all_outer_premises)
    }

    fn get_rule(&self, step: (usize, usize), sub_adrs: &Vec<usize>) -> String{
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => "Assume".to_string(),
            Some(ProofCommand::Step(ps)) => ps.rule.clone(),
            Some(ProofCommand::Subproof(sp)) => {
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => sub_ps.rule.clone(),
                    Some(_) => panic!("The last step of a subproof should be a step"),
                    None => panic!("This subproof shouldn't be empty")
                }
            }
            None => panic!("Index out of bound for the command vector")
        }
    }

    fn get_clause_len(&self, step: (usize, usize), sub_adrs: &Vec<usize>) -> usize{
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => 1,
            Some(ProofCommand::Step(ps)) => ps.clause.len(),
            Some(ProofCommand::Subproof(sp)) => {
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => sub_ps.clause.len(),
                    Some(_) => panic!("The last step of a subproof should be a step"),
                    None => panic!("This subproof shouldn't be empty")
                }
            }
            None => panic!("Index out of bound for the command vector")
        }
    }

    fn get_premises(&self, step: (usize,usize), sub_adrs: &Vec<usize>) -> Option<&Vec<(usize, usize)>>{
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => None,
            Some(ProofCommand::Step(ps)) => Some(&ps.premises),
            Some(ProofCommand::Subproof(sp)) => {
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => Some(&sub_ps.premises),
                    Some(_) => panic!("The last step of a subproof should be a step"),
                    None => panic!("This subproof shouldn't be empty")
                }
            }
            None => panic!("Index out of bound for the command vector")
        }
    }

    fn step_is_resolution(&self, step: (usize, usize), sub_adrs: &Vec<usize>) -> bool{
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Step(ps)) => ps.rule=="resolution" || ps.rule =="th-resolution",
            Some(_) => false,
            None => panic!("This command doesn't exist")
        }
    }

/*    fn collect_units_t(&mut self, sub_adrs: &Vec<usize>) -> (){
        let depth: usize = sub_adrs.len();
        //get commands and put the data of the current subproof in stack if the current proof a a subproof
        let commands_table = self.get_commands(sub_adrs);
        let commands: &Vec<ProofCommand> = commands_table[depth];
        let n = commands.len();
        let mut premise_of_resolution: HashSet<(usize,usize)> = HashSet::new(); 
        let mut pt = PartTracker::new();
        let mut outer_premises: IndexSet<(usize,usize)> = IndexSet::new();
        pt.add_step_to_part((depth,n-1),1); //adds conclusion to part 0
        for i in (0..n).rev(){
            match &commands[i]{
                ProofCommand::Assume{id, term} => {
                    println!("assume");
                }

                ProofCommand::Step(ps) => {
                    //wrong, reuse in the proper place
                    //if ps.rule == "resolution" || ps.rule == "th-resolution"{
                    //    premise_of_resolution[i] = true;
                    //}

                    // Select the parts whose the current step belong to
                    let containing;
                    match pt.parts_containing((depth,i)){
                        Ok(v) => containing = v,
                        Err(CollectionError::Node_Without_Inward_Edge) => {
                            let new_part_ind = pt.add_step_to_new_part((depth,i));
                            containing = vec![new_part_ind];
                        }
                        Err(_) => {
                            panic!("Unexpected error");
                            containing = vec![];
                        }
                    }

                    // If this node is a resolution, every premise is in the same parts
                    if ps.rule == "resolution" || ps.rule == "th-resolution" {
                        for prem in ps.premises{
                            for containing_part in containing{
                                pt.add_step_to_part(prem, containing_part)
                            }
                            // mark premises from other command vectors
                            if prem.0!=depth{
                                outer_premises.insert(prem);
                            }
                        premise_of_resolution.insert(prem);
                        } 
                    }

                    // If this node is not a resolution but is premise of a resolution,
                    // it will be in the same parts as the resolutions who use it, but its
                    // premises will be in their own parts
                    else if premise_of_resolution.contains((depth,i)){
                        for prem in ps.premises{
                            pt.add_step_to_new_part(prem);
                            if prem.0!=depth{
                                outer_premises.insert(prem);
                            }
                        }
                    }

                    // if the node is not a resolution nor premise of one
                    else {
                        for prem in ps.premises{
                            // if the premise is a resolution, it will be the conclusion of a new part
                            if self.get_rule(prem) == "resolution" || self.get_rule(prem) == "th-resolution"{
                                if prem.0!=depth{
                                    outer_premises.insert(prem);
                                } else {
                                    pt.add_step_to_new_part(prem);
                                }
                            } 
                            // if the premise is not a resolution, just add it to the part containing the current step 
                            else {
                                for containing_part in containing{
                                    pt.add_step_to_part(prem, containing_part);
                                    if prem.0!=depth{
                                        outer_premises.insert(prem);
                                    }
                                }
                            }
                        }
                    }

                    println!("proof step");

                }
                ProofCommand::Subproof(sp) => {
                    println!("subproof");
                }
            };
        }
        ()
    }
*/
    fn dive_into_proof(&self, sub_adrs: &[usize]) -> &Vec<ProofCommand>{
        let mut commands = &self.proof.commands;
        for &i in sub_adrs{
            if let ProofCommand::Subproof(sp) = &commands[i]{
                commands = &sp.commands;
            } else {
                panic!("Subproof addressing is wrong");
            }
        }
        commands
    }

    fn dive_into_proof_mut(&mut self, sub_adrs: &[usize]) -> &mut Vec<ProofCommand>{
        let mut commands = &mut self.proof.commands;
        for &i in sub_adrs{
            if let ProofCommand::Subproof(sp) = &mut commands[i]{
                commands = &mut sp.commands;
            } else {
                panic!("Subproof addressing is wrong");
            }
        }
        commands
    }
}