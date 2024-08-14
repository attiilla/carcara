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
//use std::env;
use tracker::*;
//use disjoints::*;


#[derive(Debug)]
pub struct ProofCompressor<'a>{
    pub proof: Proof,
    sp_binder: HashSet<&'static str>,
    sp_stack: Vec<&'a mut Subproof>
}




impl<'a> ProofCompressor<'a>{
    pub fn from(p: Proof)->Self{
        Self{
            proof: p,
            sp_binder: HashSet::from_iter(vec!["subproof","let","sko_ex","sko_forall","bind","onepoint"].into_iter()),
            sp_stack: Vec::new()
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
        self.lower_units(None);
        self.proof.clone()
    }

    fn lower_units(&mut self, sub: Option<&'a mut Subproof>) -> Result<(), ()> {
        let n: usize;
        match sub{
            Some(sp) => {
                self.sp_stack.push(sp);
                n = self.sp_stack.len();
            }
            None => n = 0
        };
        self.collect_units(n);
        Ok(())
    }

    fn collect_units(&mut self, depth: usize) -> (){
        let depth: usize = self.sp_stack.len();
        let commands: &Vec<ProofCommand>;
        if depth==0{
            commands = &self.proof.commands;
        }else{
            commands = &self.sp_stack[depth-1].commands;
        }
        let n = commands.len();


        let mut pt = PartTracker::new(self.is_resolution((depth,n-1)));
        let mut outer_premises: IndexSet<(usize,usize)> = IndexSet::new();
        pt.add_step_to_part((depth,n-1),1); //adds conclusion to part 1
        for i in (0..n).rev(){
            //collect_inner_units(depth,sub,premise_of_resolution,pt,outer_premises)
            match &commands[i]{
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

                    for &containing_part in &containing{
                        // Check if this step must be collected in this part
                        if pt.is_resolutions_premise_in_part((depth,i), containing_part) &&
                        pt.counting_in_part((depth,i), containing_part)>=2
                        {
                            pt.add_to_units_queue_of_part((depth,i),containing_part);
                        }
                        // Now the data in the Assume should be added to the DisjointParts of the Tracker
                        pt.clone_data_to_part((depth,i),containing_part, commands);
                    }
                }

                ProofCommand::Step(ps) => {
                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    match pt.parts_containing((depth,i)){
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => {
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i),self.is_resolution((depth,i)));
                            containing.push(new_part_ind);
                        }
                        Err(_) => panic!("Unexpected error"),
                    }

                    // If this node is a resolution, every premise is in the same parts
                    if ps.rule == "resolution" || ps.rule == "th-resolution" {
                        for &containing_part in &containing{
                            for &prem in &ps.premises{
                                pt.add_step_to_part(prem, containing_part);
                                if prem.0!=depth{ // mark premises from other command vectors
                                    outer_premises.insert(prem);
                                }
                                pt.set_resolutions_premise(prem); // marks this premise as premise of a resolution
                            }

                            // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                            pt.clone_data_to_part((depth,i),containing_part, commands);

                            // Check if this step must be collected in this part
                            if pt.counting_in_part((depth,i), containing_part)>=2 && self.get_clause_len((depth,i))==1{
                                pt.add_to_units_queue_of_part((depth,i),containing_part);
                            }
                        }
                    }

                    // If this node is not a resolution but is premise of a resolution,
                    // it will be in the same parts as the resolutions who use it, but its
                    // premises will be in their own parts if they are resolutions
                    // non-resolution premises will be in a single non-resolution part
                    else if pt.is_premise_of_resolution((depth,i)){
                        let mut premise_not_r: Vec<(usize,usize)> = vec![];
                        for &prem in &ps.premises{
                            if self.is_resolution(prem){
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
                        if premise_nor_r.len()>0{ // checks if there is a non-resolution premise
                            let non_resolution_parts = pt.non_resolution_parts((depth,i));
                            if non_resolution_parts.len()==0{ // checks if every part of this step is a resolution part, so we will create a new part
                                let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                                containing.push(new_part_ind);
                                for prem in premise_not_r{
                                    pt.add_step_to_part(prem, new_part_ind)
                                }
                            } else {
                                for containing_part in non_resolution_parts{
                                    for prem in premise_not_r{
                                        pt.add_step_to_part(prem, containing_part)
                                    }
                                }
                            }
                        }
                        
                        for &containing_part in &containing{    
                            // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                            pt.clone_data_to_part((depth,i),containing_part, commands);

                            // Check if this step must be collected in this part
                            if pt.counting_in_part((depth,i), containing_part)>=2 &&
                            self.get_clause_len((depth,i))==1 &&
                            pt.is_resolution_part(containing_part)
                            {
                                pt.add_to_units_queue_of_part((depth,i),containing_part);
                            }
                        }
                    }

                    // If the node is not a resolution nor premise of one
                    else {
                        for &prem in &ps.premises{
                            // If the premise is a resolution, it will be the conclusion of a new part
                            if self.get_rule(prem) == "resolution" || self.get_rule(prem) == "th-resolution"{
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
                            pt.clone_data_to_part((depth,i),containing_part, commands);
                        }
                    }
                }
                
                ProofCommand::Subproof(sp) => {
                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    match pt.parts_containing((depth,i)){//WARNING
                    //CORNER CASE TO TEST: Node is a subproof that isn't used as premise for any node of same depth
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => {
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i),self.is_resolution((depth,i)));
                            containing.push(new_part_ind);
                        }
                        Err(_) => panic!("Unexpected error"),
                    }
                    
                    //Get the premises of the subproof
                    let mut sp_premises: &Vec<(usize, usize)> = &vec![];
                    match self.get_premises((depth,i)){
                        Some(v) => sp_premises = v,
                        None => ()
                    }

                    //Check if the subproof is compressible in each part
                    for &containing_part in &containing{
                        if pt.is_resolutions_premise_in_part((depth,i), containing_part){

                        } else {
                            for &prem in sp_premises{
                                pt.add_step_to_part(prem, containing_part);
                            }
                        }
                    }
                }
            };
        }
        ()
    }

    fn get_rule(&self, step: (usize, usize)) -> String{
        let depth = step.0;
        let ind = step.1;
        let commands: &Vec<ProofCommand>;
        if depth==0{
            commands = &self.proof.commands;
        } else{
            match self.sp_stack.get(depth-1){
                Some(v) => commands = &v.commands,
                None => panic!("Index out of bounds. There is a step with a depth larger than the subproof stack.")
            }
        }
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

    fn get_clause_len(&self, step: (usize, usize)) -> usize{
        let depth = step.0;
        let ind = step.1;
        let commands: &Vec<ProofCommand>;
        if depth==0{
            commands = &self.proof.commands;
        } else{
            match self.sp_stack.get(depth-1){
                Some(v) => commands = &v.commands,
                None => panic!("Index out of bounds. There is a step with a depth larger than the subproof stack.")
            }
        }
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

    fn get_premises(&self, step: (usize,usize)) -> Option<&Vec<(usize, usize)>>{
        let depth = step.0;
        let ind = step.1;
        let commands: &Vec<ProofCommand>;
        if depth==0{
            commands = &self.proof.commands;
        } else{
            match self.sp_stack.get(depth-1){
                Some(v) => commands = &v.commands,
                None => panic!("Index out of bounds. There is a step with a depth larger than the subproof stack.")
            }
        }
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

    fn is_resolution(&self, step: (usize, usize)) -> bool{
        let depth = step.0;
        let ind = step.1;
        let commands: &Vec<ProofCommand>;
        if depth==0{
            commands = &self.proof.commands;
        } else{
            match self.sp_stack.get(depth-1){
                Some(v) => commands = &v.commands,
                None => panic!("Index out of bounds. There is a step with a depth larger than the subproof stack.")
            }
        }
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

    fn get_commands(&mut self, sub_adrs: &Vec<usize>) -> Vec<&Vec<ProofCommand>>{
        let mut commands_table: Vec<&Vec<ProofCommand>> = vec![];
        let mut commands = &self.proof.commands;
        commands_table.push(commands);
        for i in 0..sub_adrs.len(){
            let ind = sub_adrs[i];
            if let ProofCommand::Subproof(sp) = &commands[ind]{
                commands = &sp.commands;
                commands_table.push(commands);
                if i == sub_adrs.len()-1{
                    self.sp_stack.push(sp.args.clone());
                }
            } else {
                panic!("Subproof addressing is wrong");
            }
        }
        commands_table
    }
*/
}