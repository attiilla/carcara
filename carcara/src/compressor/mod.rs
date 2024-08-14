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
        let mut premise_of_resolution: HashSet<(usize,usize)> = HashSet::new();
        let mut pt = PartTracker::new();
        let mut outer_premises: IndexSet<(usize,usize)> = IndexSet::new();
        pt.add_step_to_part((depth,n-1),1); //adds conclusion to part 1
        for i in (0..n).rev(){
            //collect_inner_units(depth,sub,premise_of_resolution,pt,outer_premises)
            match &commands[i]{
                ProofCommand::Assume{id, term} => {
                    println!("assume");
                }

                ProofCommand::Step(ps) => {
                    // Select the parts whose the current step belong to
                    let mut containing: Vec<usize> = vec![];
                    match pt.parts_containing((depth,i)){
                        Ok(v) => containing = v,
                        Err(CollectionError::NodeWithoutInwardEdge) => {
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i));
                            containing.push(new_part_ind);
                        }
                        Err(_) => {
                            panic!("Unexpected error");
                        }
                    }

                    // If this node is a resolution, every premise is in the same parts
                    if ps.rule == "resolution" || ps.rule == "th-resolution" {
                        for &prem in &ps.premises{
                            for &containing_part in &containing{
                                pt.add_step_to_part(prem, containing_part)
                            }
                            // mark premises from other command vectors
                            if prem.0!=depth{
                                outer_premises.insert(prem);
                            }
                        premise_of_resolution.insert(prem);
                        } 
                        //add collect checking and part copying
                    }

                    // If this node is not a resolution but is premise of a resolution,
                    // it will be in the same parts as the resolutions who use it, but its
                    // premises will be in their own parts
                    else if premise_of_resolution.contains(&(depth,i)){
                        for &prem in &ps.premises{
                            pt.add_step_to_new_part(prem);
                            if prem.0!=depth{
                                outer_premises.insert(prem);
                            }
                        }
                        //add collect checking and part copying
                    }


                    // if the node is not a resolution nor premise of one
                    else {
                        for &prem in &ps.premises{
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
                                for &containing_part in &containing{
                                    pt.add_step_to_part(prem, containing_part);
                                    if prem.0!=depth{
                                        outer_premises.insert(prem);
                                    }
                                }
                            }
                        }
                        //add part copying
                    }
                    
                    for &containing_part in &containing{
                        // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                        pt.clone_data_to_part((depth,i),containing_part, commands);

                        // Here we check if it must be collected this part
                        if pt.counting_in_part((depth,i), containing_part)>=2 && self.get_clause_len((depth,i))==1{//WARNING
                            pt.add_to_units_queue_of_part((depth,i),containing_part);
                        }
                    }

                }
                ProofCommand::Subproof(sp) => {
                    println!("subproof");
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