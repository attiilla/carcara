//Question: outer_premises that aren't resolution can be thrown out after cloning their data to the parts?
//Only steps that are resolution and are premise of another resolution are compressed by lower units

mod tracker;
mod disjoints;
mod error;
use crate::ast::term::Term;
use crate::checker::rules::Premise;
use crate::compressor::error::*;
use crate::ast::proof::*;
use crate::ast::pool::PrimitivePool;
//use crate::ast::node::*;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;
//use std::ops::Index;
//use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
use crate::ast::rc::Rc;
use disjoints::DisjointPart;
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
                    let args = format!(", args: {:?}", &ps.args);
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

    pub fn compress_proof(&mut self, proof_pool: &mut PrimitivePool) -> Proof{
        env::set_var("RUST_BACKTRACE", "1");
        print_proof(&self.proof.commands, "".to_string(), 0);
        let _ = self.lower_units(vec![], 0, proof_pool);
        self.proof.clone()
    }

    fn lower_units(&mut self, sub_adrs: Vec<usize>, debug_aux: usize, proof_pool: &mut PrimitivePool) -> Result<IndexSet<(usize,usize)>, ()> {
        let (mut pt, premises_from_sub) = self.collect_units(&sub_adrs, debug_aux, proof_pool);
        let global_to_local_tables = self.fix_broken_proof(&mut pt, &sub_adrs, proof_pool);
        for part in pt.parts{
            println!("{:?}",part);
        }
        Ok(premises_from_sub)
    }

    fn collect_units(&mut self, sub_adrs: &Vec<usize>, debug_aux: usize, proof_pool: &mut PrimitivePool) -> (PartTracker, IndexSet<(usize,usize)>){
        let depth: usize = sub_adrs.len();
        let (subproof_to_outer_premises, outer_premises)= self.process_subproofs(sub_adrs, debug_aux+1, proof_pool);
        let mut outer_premises: IndexSet<(usize,usize)> = outer_premises.into_iter().filter(|&(d, i)| d != depth).collect();
        
        let fixed_clauses: Vec<(usize,usize)> = outer_premises.iter().filter( |&&x | x.0==depth).cloned().collect();
        let mut outer_premises: IndexSet<(usize,usize)> = outer_premises.iter().filter( |&&x | x.0<depth).cloned().collect();

        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        //if debug_aux==1{println!("What? {:?}",&commands[12]);}
        let n = commands.len();
        let mut pt = PartTracker::new(self.step_is_resolution((depth,n-1), sub_adrs), sub_adrs.len());
        for prem in fixed_clauses{
            pt.set_cant_be_deleted(prem); // Forbids the compression algorithm of deleting steps that are used as premises in subproofs
        }
        pt.add_step_to_part((depth,n-1),1); //adds conclusion to part 1
        pt.set_is_conclusion((depth,n-1));
        for (i, c) in commands.iter().enumerate().rev(){
            match c{
                ProofCommand::Assume{id, term} => {
                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    pt.add_step_to_part((depth,i), 0); //all assumes must be in the part 0
                    match pt.parts_containing((depth,i)){
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => 
                            panic!("This error should be impossible in this part of the code.\nThis node was added to part 0 just some lines above"),
                        Err(_) => panic!("Unexpected error"),
                    }
                    /*
                    if debug_aux==1 {
                        println!("O passo {:?} pertence as partes {:?}", i, &containing);
                    }*/
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
                    /*if debug_aux==1{
                        println!("O passo {:?} pertence as partes {:?}", i, &containing);
                    }*/

                    // Case 1
                    // If this node is a resolution, every premise is in the same parts
                    if ps.rule == "resolution" || 
                    ps.rule == "th-resolution" || 
                    (ps.rule=="contraction" && self.resolution_is_a_premise(&ps, sub_adrs)){
                        // First we check if this is one of the steps that can't be deleted
                        // If it isn't conclusion of a part and can't be deleted, we create a 
                        // new part with this step as conclusion
                        if pt.must_be_a_new_conclusion((depth,i)){
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i), true);
                            containing.push(new_part_ind);
                            /*if debug_aux==1{
                                println!("_Agora o passo {:?} pertence as partes {:?}", i, &containing);
                            }*/
                        }
                        /*if debug_aux==1{
                            println!("A essas partes serão adicionados os passos {:?}\n\n", &ps.premises);
                        }*/
                        for &containing_part in &containing{
                            for &prem in &ps.premises{
                                pt.add_step_to_part(prem, containing_part);
                                if prem.0!=depth{ // mark premises from other command vectors
                                    outer_premises.insert(prem);
                                    pt.set_cant_be_deleted(prem);//WARNING
                                }
                                if ps.rule == "resolution" || ps.rule == "th-resoltion"{
                                    pt.set_resolutions_premise(prem); // marks this premise as premise of a resolution if this is a resolution
                                } else if ps.rule == "contraction" && pt.is_premise_of_resolution((depth,i)){
                                    pt.set_resolutions_premise(prem); // if its a contraction, mark the premise only if the contraction was premise of a resolution
                                }
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
                        if ps.rule!="or"{ //check if the rule is an or, in this case it's premise already is going to be added to part 0
                            // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
                            // or create a single part for this node and all it's non-resolution premises
                            if premise_not_r.len()>0{ // checks if there is a non-resolution, and if step is not or
                                let non_resolution_parts = pt.non_resolution_parts((depth,i));
                                if debug_aux==1 && i==8{
                                    println!("non_resolution_parts: {:?}",&non_resolution_parts);
                                }
                                if non_resolution_parts.len()==0{ // checks if every part of this step is a resolution part, so we will create a new part
                                    let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                                    containing.push(new_part_ind);
                                    for &prem in &premise_not_r{
                                        pt.add_step_to_part(prem, new_part_ind)
                                    }
                                } else{
                                    for &containing_part in &non_resolution_parts{
                                        for &prem in &premise_not_r{
                                            pt.add_step_to_part(prem, containing_part)
                                        }
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
                        /*if debug_aux==1{
                            println!("O passo {:?} pertence as partes {:?}",i, &containing);               
                        }*/
                        //let mut r_prems: Vec<(usize,usize)> = vec![]; //To_delete
                        //let mut n_parts: Vec<i32> = vec![]; //To_delete
                        for &prem in &ps.premises{
                            // If the premise is a resolution, it will be the conclusion of a new part
                            if self.get_rule(prem, sub_adrs) == "resolution" || self.get_rule(prem, sub_adrs) == "th-resolution"{
                                if prem.0!=depth{
                                    outer_premises.insert(prem);
                                    /*r_prems.push(prem);
                                    n_parts.push(-1);
                                    if outer_premises.insert(prem){
                                        println!("{:?} inserted to outer premises in location 3 on level {:?}", prem, debug_aux);
                                    }*/
                                }/* else {
                                    r_prems.push(prem);
                                    let u = pt.add_step_to_new_part(prem,true) as i32;
                                    n_parts.push(u);
                                }*/
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
                
                ProofCommand::Subproof(sp) => {//WARNING Corner Case: Let com premissa em outra profundidade
                    //if debug_aux==1 {println!("id: {:?}", Self::subproof_id(sp))};
                    let sp_premises: Vec<(usize,usize)>;
                    match subproof_to_outer_premises.get(&i){
                        Some(v) => sp_premises = v.iter().cloned().collect(),
                        None => panic!("No outer premises. Add an empty set to the structure if a subproof has no outer premise")
                    };
                    let same_depth_premises: Vec<(usize,usize)> = sp_premises.iter().filter( |&&x | x.0==depth).cloned().collect();
                    //let other_depth_premises: Vec<(usize,usize)> = sp_premises.iter().filter( |&&x | x.0<depth).cloned().collect();
                    //outer_premises.extend(other_depth_premises);  //already processed

                    
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

                    /*if debug_aux==1{
                        println!("No passo {:?}, as \"premissas\" de mesma profundidade são {:?}", i, &last_step_and_same_depth_premises);
                    }*/
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
                                pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions of same depth
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
                }
            };
        }
        // Now we will clone the data from outer premises in the respective parts
        // WARNING: After debugging this entire loop might be deleted
        for &outer_step in outer_premises.iter(){
            let mut containing: Vec<usize> = vec![];
            match pt.parts_containing(outer_step){
                Ok(v) => containing = v,
                Err(_) => {
                    containing = vec![];
                }
            }
            let outer_commands: &Vec<ProofCommand> = self.dive_into_proof(&sub_adrs[0..outer_step.0]);
            for containing_part in containing.into_iter(){
                pt.clone_data_to_part(outer_step, containing_part, outer_commands, Some(vec![]));
            }
        }

        (pt,outer_premises)
    }

    fn fix_broken_proof(&mut self, pt: &mut PartTracker, sub_adrs: &Vec<usize>, proof_pool: &mut PrimitivePool) -> Vec<HashMap<(usize,usize),usize>>{
        let mut subs_table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
        let mut ans = vec![];
        for p in pt.parts.iter_mut(){
            let mut global_to_local: HashMap<(usize,usize),usize> = HashMap::new();
            if p.compressible{
                //self.fill_local_premises(p);
                for step in p.part_commands.iter_mut().rev(){
                    global_to_local.insert(step.proof_ind.unwrap(),step.ind);
                    let op_index = step.proof_ind;
                    if let Some(index) = op_index {
                        if p.all_premises_remain(step) || p.some_premises_remains(step){
                            let (clause, prem, args) = self.re_resolve(p, step.ind, sub_adrs, proof_pool);
                            step.clause = clause;
                            step.premises = prem.iter().map(|premise| premise.index).collect();
                            step.args = args;
                        }
                        else if p.single_premise_remains(step){
                            p.substitute(&mut subs_table, index, p.remaining_premises(step)[0]);
                        }
                        else {
                            panic!("This doesn't seemed to be possible");
                        }
                    } else {
                        //WARNING: untreated case
                    }
                }
            }
            ans.push(global_to_local);
        }
        ans
    }

    fn process_subproofs(&mut self, sub_adrs: &Vec<usize>, debug_aux: usize, proof_pool: &mut PrimitivePool) -> (HashMap<usize,IndexSet<(usize,usize)>>, IndexSet<(usize,usize)>){
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
                let sp_result = self.lower_units(new_sub_adrs, debug_aux, proof_pool);
                println!("Emerging from subproof {i} of depth {debug_aux}");
                match sp_result{
                    Ok(sp_premises) => {
                        all_outer_premises.extend(sp_premises.iter());
                        subproofs_to_outer_premises.insert(i, sp_premises);
                    },
                    Err(_) => panic!("Some subproof coudn't be compressed")
                }
            }else{
                panic!("There is an error in the logic. This index is computed as the index of a subproof, yet there is no subproof in this index")
            }
        }
        println!("Subproofs to outer premises in level {:?}: {:?}", debug_aux, &subproofs_to_outer_premises);
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

    fn resolution_is_a_premise(&self, step: &ProofStep, sub_adrs: &Vec<usize>) -> bool{
        if step.premises.len()!=1{
            panic!("Contraction from not exactly 1 premise");
        } else {
            let contracted_from = step.premises[0];
            let (depth, ind) = contracted_from;
            let commands: &Vec<ProofCommand> = self.dive_into_proof(&sub_adrs[0..depth]);
            match commands.get(ind){
                Some(ProofCommand::Step(ps)) => {
                    if ps.rule == "resolution" || ps.rule == "th-resolution"{
                        true
                    } else {
                        false
                    }
                }
                Some(_) => false,
                None => panic!("This command doesn't exist")
            }
        }
    }

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

    fn subproof_id(sp: &Subproof) -> String{
        match sp.commands.last().unwrap(){
            ProofCommand::Step(ps) => ps.id.clone(),
            _ => panic!("The end of a subproof should always be a step")
        }
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

    fn re_resolve(&self, 
        part: &mut DisjointPart, 
        index: usize, 
        sub_adrs: &Vec<usize>, 
        proof_pool: &mut PrimitivePool
    ) -> 
    (Vec<Rc<Term>>,Vec<Premise<'_>>,Vec<ProofArg>){
        let step = &part.part_commands[index];
        let remaining = part.remaining_premises(step);
        let premises = self.build_premises(part, &remaining, index, sub_adrs);
        let args = self.build_args(part, &remaining, index, sub_adrs);
        let resolution: Result<IndexSet<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<IndexSet<_>>(&premises, &args, proof_pool);
        match resolution{
            Ok(r) => {
                let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();    
                let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                (resolvent, premises, args)
            }
            _ => panic!("Error: Clauses couldn't be resolved\n
                    Resolving for {:?} on part {:?}\n
                    Premises: {:?}\n
                    Arguments: {:?}", 
                    index, part.ind, premises, args),
        }
    }

    fn build_premises(&self, part: &DisjointPart, remaining: &Vec<(usize, usize)>, index: usize, sub_adrs: &Vec<usize>) -> Vec<Premise>{
        let mut ans: Vec<Premise> = vec![];
        let commands = self.dive_into_proof(sub_adrs);
        let data = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().cloned().collect();
        for p in data.premises.iter(){
            if remaining_set.contains(p){
                ans.push(Premise::new(*p,&commands[p.1]));
            }
        }
        ans
    }

    fn build_args(&self, part: &DisjointPart, remaining: &Vec<(usize, usize)>, index: usize, sub_adrs: &Vec<usize>) -> Vec<ProofArg>{
        let mut ans: Vec<ProofArg> = vec![];
        let data = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().cloned().collect();
        let old_args = &data.args; 
        if remaining_set.contains(&data.premises[0]){
            ans.push(old_args[0].clone());
            ans.push(old_args[1].clone());
        }
        for (i, &p) in data.premises.iter().skip(2).enumerate(){
            if remaining_set.contains(&p){
                let j = i+2;
                ans.push(old_args[2*j-2].clone());
                ans.push(old_args[2*j-1].clone());
            }
        }
        ans
    }
}