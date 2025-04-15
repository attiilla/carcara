//Question: outer_premises that aren't resolution can be thrown out after cloning their data to the parts?
//Only steps that are resolution and are premise of another resolution are compressed by lower units
//benchmarks/small/SH_problems_all_filtered/Green_veriT/x2020_07_28_19_01_13_405_7253502.smt2 rodando ~/carcara/wt-atila/target/release/carcara check -i --allow-int-real-subtyping --expand-let-bindings test.alethe x2020_07_28_19_01_13_405_7253502.smt2
//Uncontracted resolution with two pivots in one premise
//build_term!(pool, (not { term }))
mod tracker;
mod disjoints;
mod error;
use crate::ast::term::Term;
use crate::ast::rc::Rc;
use crate::checker::rules::Premise;
use crate::compressor::error::*;
use crate::ast::proof::*;
use crate::ast::pool::PrimitivePool;
//use crate::ast::node::*;
use std::collections::{HashSet, HashMap};
use std::{mem, vec};
//use std::ops::Index;
//use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution, binary_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
use disjoints::*;
use indexmap::IndexSet;
use std::env;
use tracker::*;


#[derive(Debug)]
pub struct ProofCompressor{
    proof: Proof,
    sp_binder: HashSet<String>, //list of rules that implie that a step opens a subproof
    preserving_binder: HashSet<String>, //list of rules that don't break a disjoint part of resolutions
    subproofs: Vec<SubproofMeta>, //subproofs of the proof with the clauses from them that must not be deleted
    
    // Maps the steps that can't be deleted to their indexes in the new proof
    // The values are all None, until rebuild fills it with index
    // of the Commands inside the new proof being build
    fixed: HashMap<(usize,usize), Option<(usize,usize)>>,

    // Maps the outer steps used by the proof to their sub_adrs
    // Always empty here, added just to make the code more readable
    outer: HashMap<(usize,usize), Option<usize>>,

}

#[derive(Debug)]
struct SubproofMeta{
    proof: Subproof,
    fixed: HashMap<(usize,usize),Option<(usize,usize)>>, // premises that can't be deleted are the keys, their updated indexes are the values
    depth: usize,
    outer: HashMap<(usize,usize),Option<usize>>, // Maps outer premises to owners sub_adrs
    new_ind: usize,
    parent_adrs: Option<usize>,
    discharge: Vec<(usize,usize)>,

}

#[derive(Debug)]
struct ReResolveInfo{
    substitute: bool,
    location: usize,
    index: (usize, usize),
}


impl<'a> ProofCompressor{
    pub fn from(p: Proof)->Self{
        Self{
            proof: p,
            sp_binder: vec![
                            "subproof".to_owned(),
                            "let".to_owned(),
                            "sko_ex".to_owned(),
                            "sko_forall".to_owned(),
                            "bind".to_owned(),
                            "onepoint".to_owned()
                        ].into_iter().collect::<HashSet<_>>(),
            preserving_binder:  vec![
                                    "contraction".to_owned()/* ,
                                    "reordering".to_owned()*/
                                ].into_iter().collect::<HashSet<_>>(),
            subproofs: Vec::new(),
            fixed: HashMap::new(),
            outer: HashMap::new(),
        }
    }

    pub fn compress_proof(mut self, proof_pool: &mut PrimitivePool) -> Proof{
        env::set_var("RUST_BACKTRACE", "1");
        //print_proof(&self.proof.commands, "".to_string(), 0, 0);
        //println!("carimbada");
        let _ = &mut self.lower_units(None,  proof_pool);
        // remove the placeholders and insert the subproofs again in the final proof
        self.reassemble();
        //print_proof(&self.proof.commands, "".to_string(), 0, 0);
        self.proof
    }

    fn lower_units(&mut self, sub_adrs: Option<usize>, proof_pool: &mut PrimitivePool) {
        // Check for steps that can't be deleted and subproof locations
        // Collect every subproof into an array and replace them with placeholders
        if sub_adrs.is_none(){
            self.relocate_subproofs(sub_adrs);
        }
        
        // break the proof in parts that has only resolution and preserving binders
        // collect units
        let mut pt: PartTracker = self.collect_units(sub_adrs, proof_pool);
        /*if sub_adrs.is_none(){
            println!("Before fix");
            self.print_part(&pt.parts[1]);
        }*/
        // turn every part of a proof in a valid reasoning
        self.fix_broken_proof(&mut pt, sub_adrs, proof_pool);
        /*if sub_adrs.is_none(){
            println!("After fix");
            self.print_part(&pt.parts[1]);
        }*/
        // reinsert the collected units to each part
        self.reinsert_collected_clauses(&mut pt, sub_adrs, proof_pool);
        /*if sub_adrs.is_none(){
            println!("After reinsert");
            self.print_part(&pt.parts[1]);
        }*/
        
        // combines the parts to create a valid proof
        let new_commands: Vec<ProofCommand> = self.rebuild(&mut pt, sub_adrs);
        self.position_insert(new_commands, sub_adrs);

        //calls this same algorithm over every subproof
        if sub_adrs.is_none(){
            for i in 0..self.subproofs.len(){
                self.lower_units(Some(i), proof_pool);
            }
        }
    }

    fn lower_units_verbose(&mut self, sub_adrs: Option<usize>, proof_pool: &mut PrimitivePool) {
        // Check for steps that can't be deleted and subproof locations
        // Collect every subproof into an array and replace them with placeholders
        if sub_adrs.is_none(){
            self.relocate_subproofs(sub_adrs);
        }
        println!("Proof:");
        println!("Fixed: {:?}",&self.fixed);
        println!("Outer: {:?}",&self.outer);
        for (i, mt_sp) in self.subproofs.iter().enumerate(){
            println!("Meta {:?}:",i);
            println!("Fixed {:?}",&mt_sp.fixed);
            println!("Outer: {:?}",&mt_sp.outer);
        }

        // break the proof in parts that has only resolution and preserving binders
        // collect units
        let mut pt: PartTracker = self.collect_units(sub_adrs, proof_pool);
        for p in &pt.parts{
            self.print_part(p);
            println!("Collected: {:?}", &p.units_queue);
        }
        /*if pt.parts.iter().fold(0, |acc, part| acc+part.units_queue.len()) == 0{
            return;
        }*/
        
        // turn every part of a proof in a valid reasoning
        self.fix_broken_proof(&mut pt, sub_adrs, proof_pool);
        println!("after fix");
        for p in &pt.parts{
            self.print_part(p);
            println!("Substituted: {:?}",&p.subs_table);
        }
        

        // reinsert the collected units to each part
        self.reinsert_collected_clauses(&mut pt, sub_adrs, proof_pool);
        for p in &pt.parts{
            println!("New conclusion part {:?}: {:?}", &p.ind, &p.new_conclusion);
        }


        // combines the parts to create a valid proof
        let new_commands: Vec<ProofCommand> = self.rebuild(&mut pt, sub_adrs);
        //println!("New commands {:?}", &new_commands);
        println!("Socorro Naldo!!!!");
        print_proof(&new_commands, "".to_string(), 0, 0);
        self.position_insert(new_commands, sub_adrs);
        

        //calls this same algorithm over every subproof
        if sub_adrs.is_none(){
            for i in 0..self.subproofs.len(){
                self.lower_units_verbose(Some(i), proof_pool);
            }
        }
    }

    // Returns None if the owner is not a subproof
    fn fetch_owner_subproof(&self, sub_adrs: Option<usize>, tgt: usize) -> Option<usize>{ //ok //Change
        if tgt==0{
            None
        } else {
            match sub_adrs{
                None => panic!("This is a step from the level 0. There's no superproof of higher level"),
                Some(v) => {
                    let mut candidate = v-1;
                    loop{
                        if self.subproofs[candidate].depth == tgt{
                            return Some(candidate);
                        }
                        candidate-=1;
                    }
                }
            }
        }
    }

    fn relocate_subproofs(&mut self, sub_adrs: Option<usize>){ //ok
        let depth = match &sub_adrs{
            Some(v) => self.subproofs[*v].depth,
            None => 0
        };

        let mut subproof_indexes: Vec<usize> = vec![];
        let mut fixed_clauses: Vec<(usize,usize)> = vec![];
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        for (i, c) in commands.iter().enumerate(){ //finds subproofs and outer premises
            match c{
                ProofCommand::Assume{..} => (),
                ProofCommand::Step(ps) => {
                    for &prem in &ps.premises{
                        if prem.0!=depth{
                            fixed_clauses.push(prem); //lists outer premise
                        }
                    }
                }
                ProofCommand::Subproof(_) => {
                   subproof_indexes.push(i); //anotate subproof location
                }
            }
        }
        
        for &prem in &fixed_clauses{ //set the clauses as fixed
            let me: usize = match sub_adrs{
                None => panic!("Dead code, i hope"),
                Some(v) => v
            };

            if prem.0==0{
                self.fixed.insert(prem,None);
                self.subproofs[me].outer.insert(prem,None);
            } else {
                let owner_op: Option<usize> = self.fetch_owner_subproof(sub_adrs, prem.0);
                let fixed: &mut HashMap<(usize,usize),Option<(usize,usize)>> = match owner_op{
                    None => &mut self.fixed,
                    Some(owner) => &mut self.subproofs[owner].fixed,
                };
                fixed.insert(prem,None);
                
                self.subproofs[me].outer.insert(prem, owner_op);
            }
        }
        

        for i in subproof_indexes{ //send subproofs to self.subproofs and calls function recursively on them
            let extracted_sp: Subproof;
            {
                let sp_id = self.subproofs.len();
                let m_commands: &mut Vec<ProofCommand> = self.dive_into_proof_mut(sub_adrs);
                if let ProofCommand::Subproof(sp) = &mut m_commands[i]{
                    let ph = sp.new_placeholder(sp_id);
                    extracted_sp = mem::replace(sp,ph);
                } else {
                    panic!("This should be a subproof");
                }
            }
            self.subproofs.push(
                SubproofMeta{
                    proof: extracted_sp,
                    fixed: HashMap::new(),
                    depth: depth+1,
                    outer: HashMap::new(),
                    new_ind: i,
                    parent_adrs: sub_adrs,
                    discharge: vec![],
                }
            );
            self.relocate_subproofs(Some(self.subproofs.len()-1));
        }
    }

    fn collect_units(&mut self, sub_adrs: Option<usize>, proof_pool: &mut PrimitivePool) -> PartTracker{
        
        let mut outer_premises: IndexSet<(usize,usize)> = IndexSet::new();
        let depth: usize = match sub_adrs{
            Some(v) => self.subproofs[v].depth,
            None => 0,
        };
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        let n = commands.len();
        let mut pt = PartTracker::new(self.step_is_resolution((depth,n-1), sub_adrs));
        /*for prem in fixed_clauses{
            pt.set_cant_be_deleted(prem); // Prohibits the compression algorithm from deleting steps that are used as premises in subproofs
        }*/
        pt.add_step_to_part((depth,n-1),1); //adds conclusion to part 1
        //println!("Add {:?} to part 1",(depth,n-1));
        pt.set_is_conclusion((depth,n-1));
        for (i, c) in commands.iter().enumerate().rev(){
            //println!("i is {:?} and the number of parts is {:?}", i, &pt.parts.len());
            //println!("Command is {:?}",c);
            match c{
                ProofCommand::Assume{id,term} => {
                    // Select the parts whose the current step belong to
                    pt.add_step_to_part((depth,i), 0); //all assumes must be in the part 0
                    let containing: Vec<usize> = match pt.parts_containing((depth,i)){
                        Ok(v) => v,
                        Err(CollectionError::NodeWithoutInwardEdge) => 
                            panic!("This error should be impossible in this part of the code.\nThis node was added to part 0 just some lines above"),
                        Err(_) => panic!("Unexpected error"),
                    };

                    //println!("Parts containing Assume {id}: {term}\n{:?}",&containing);
                    for &containing_part in &containing{
                        let position = pt.parts[containing_part].part_commands.len();
                        // The data in the Assume should be added to the DisjointParts of the Tracker
                        pt.clone_data_to_part((depth,i),containing_part, commands);

                        // Check if this step must be collected in this part
                        let req: usize = if self.is_premise_of_part_conclusion(containing_part, (depth,i), &pt){
                            3
                        }else{
                            2
                        };
                        if pt.is_premise_of_resolution((depth,i)) &&
                        pt.counting_in_part((depth,i), containing_part)>=req &&
                        pt.is_resolution_part(containing_part)
                        {
                            //println!("Adding Assume {id}: {term} to queue of part {:?}",&containing_part);
                            pt.add_to_units_queue_of_part((depth,i),containing_part, position, &self.subproofs, proof_pool);
                        }
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

                    // Case 1
                    // If this node is a resolution, every premise is in the same parts
                    if ps.rule == "resolution" || 
                    ps.rule == "th-resolution" || 
                    (self.preserving_binder.contains(&ps.rule) && self.resolution_is_a_premise(&ps, sub_adrs)){
                        // First we check if this is one of the steps that can't be deleted
                        // If it isn't conclusion of a part and can't be deleted, we create a 
                        // new part with this step as conclusion

                        if self.must_be_a_new_conclusion((depth,i), &pt, sub_adrs){
                            let new_part_ind: usize = pt.add_step_to_new_part((depth,i), true);
                            containing.push(new_part_ind);
                        }
                        if self.preserving_binder.contains(&ps.rule){
                            for &containing_part in &containing{
                                pt.set_as_behaved(ps.premises[0],containing_part);       
                            }
                        }

                        for &containing_part in &containing{
                            for &prem in &ps.premises{
                                if prem.0!=depth{
                                    outer_premises.insert(prem);
                                }
                                pt.add_step_to_part(prem, containing_part);
                                if ps.rule == "resolution" || ps.rule == "th-resoltion"{
                                    pt.set_resolutions_premise(prem); // marks prem as premise of a resolution if this is a resolution
                                } else if self.preserving_binder.contains(&ps.rule) && pt.is_premise_of_resolution((depth,i)){
                                    pt.set_resolutions_premise(prem); // if its a contraction/reordering, mark prem only if this step is premise of a resolution
                                }
                            }
                            

                            // Now the data in the ProofCommand is added to the DisjointParts of the Tracker
                            let position = pt.parts[containing_part].part_commands.len();
                            pt.clone_data_to_part((depth,i), containing_part, commands);

                            // Check if this step must be collected in this part
                            // The step have to be used as premise 2 times to nodes that are not the conclusion
                            // So, if it is premise to the conclusion it has to be premise 3 times
                            let req: usize = 
                                if self.is_premise_of_part_conclusion(containing_part, (depth,i), &pt){ 3 }else{ 2 };
                            if pt.counting_in_part((depth,i), containing_part)>=req && self.get_clause_len((depth,i), sub_adrs)==1{
                                pt.add_to_units_queue_of_part((depth,i),containing_part, position, &self.subproofs, proof_pool);
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
                            if prem.0==depth{
                                if self.step_is_resolution(prem, sub_adrs){
                                    pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions
                                    //println!("Now there are {:?} parts",&pt.parts.len());
                                    //println!("Last part is {:?}",&pt.parts.last().unwrap());
                                } else {
                                    premise_not_r.push(prem); // stores the premises that aren't resolutions
                                }
                            }
                        }
                        if !self.single_assume_is_premise((depth,i), commands, sub_adrs){ //check if this step comes from an assume, 
                            // In this case it's premise already is going to be added to part 0.
                            // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
                            // or create a single part for this node and all it's non-resolution premises
                            if !premise_not_r.is_empty(){ // checks if there is a non-resolution, and if step is not or
                                let non_resolution_parts = pt.non_resolution_parts((depth,i));
                                
                                if non_resolution_parts.is_empty(){ // checks if every part of this step is a resolution part, so we will create a new part
                                    let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                                   // containing.push(new_part_ind);
                                    for &prem in &premise_not_r{
                                        pt.add_step_to_part(prem, new_part_ind);
                                    }
                                } else{
                                    for &containing_part in &non_resolution_parts{
                                        for &prem in &premise_not_r{
                                            pt.add_step_to_part(prem, containing_part);
                                        }
                                    }
                                }
                            }
                        }
                        
                        // Now the data in the ProofCommand is added to the DisjointParts of the Tracker
                        for &containing_part in &containing{
                            let position = pt.parts[containing_part].part_commands.len();
                            pt.clone_data_to_part((depth,i),containing_part, commands);

                            if pt.parts[containing_part].compressible{
                                // Check if this step must be collected in this part
                                let req: usize = if self.is_premise_of_part_conclusion(containing_part, (depth,i), &pt){
                                    3
                                }else{
                                    2
                                };
                                if pt.counting_in_part((depth,i), containing_part)>=req && self.get_clause_len((depth,i), sub_adrs)==1{
                                    pt.add_to_units_queue_of_part((depth,i),containing_part, position, &self.subproofs, proof_pool);
                                }
                            }
                        }

                    }

                    // Case 3
                    // If the node is not a resolution nor premise of one
                    else {
                        for &prem in &ps.premises{
                            if prem.0==depth{
                                // If the premise is a resolution, it will be the conclusion of a new part
                                if self.step_is_resolution(prem, sub_adrs){
                                    pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions
                                } 
                                // If the premise is not a resolution, just add it to the parts containing the current step 
                                else {
                                    for &containing_part in &containing{
                                        pt.add_step_to_part(prem, containing_part);
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
                
                ProofCommand::Subproof(ph_sp) => {//WARNING Corner Case: Let com premissa em outra profundidade
                    let sp = self.access_subproof(&ph_sp);
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
                    
                    
                    let premises = match sp.commands.last(){
                        None => panic!("Why there is an empty subproof on your proof?"),
                        Some(ProofCommand::Step(ps)) => &ps.premises,
                        _ => panic!("Why does your proof has an subproof that doesn't end in a step?"),
                    };

                    // If the subproof is not premise of a resolution, it's resolution premises of same depth will be conclusion of new parts
                    // and it's other premises will be added to it's parts
                    if pt.is_premise_of_resolution((depth,i)){
                        let mut premise_not_r: Vec<(usize,usize)> = vec![];
                        for &prem in premises{
                            if prem.0==depth{
                                if self.step_is_resolution(prem, sub_adrs){
                                    pt.add_step_to_new_part((depth,i), true); // creates new parts for the premises that are resolutions
                                } else {
                                    premise_not_r.push(prem); // stores the premises that aren't resolutions
                                }
                            }
                        }
                        
                        // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
                        // or create a single part for this node and all it's non-resolution premises
                        if !premise_not_r.is_empty(){ // checks if there is a non-resolution, and if step is not or
                            let non_resolution_parts = pt.non_resolution_parts((depth,i));
                            if non_resolution_parts.is_empty(){ // checks if every part of this step is a resolution part, so we will create a new part
                                let new_part_ind: usize = pt.add_step_to_new_part((depth,i), false);
                                containing.push(new_part_ind);
                                for &prem in &premise_not_r{
                                    pt.add_step_to_part(prem, new_part_ind);
                                }
                            } else{
                                for &containing_part in &non_resolution_parts{
                                    for &prem in &premise_not_r{
                                        pt.add_step_to_part(prem, containing_part);
                                    }
                                }
                            }
                        }
                    }
                    // If the subproof is premise of a resolution
                    // A logic much like the Case 2 of ProofStep will be used
                    else{
                        for &prem in premises{
                            if prem.0==depth{
                                if self.step_is_resolution(prem, sub_adrs) && prem.0==depth{
                                    pt.add_step_to_new_part(prem, true);
                                } else {
                                    for &containing_parts in &containing {
                                        pt.add_step_to_part(prem, containing_parts);
                                    }
                                }
                            }
                        }

                    }
                    // Now the data in the placeholder should be added to the DisjointParts of the Tracker
                    for &containing_part in &containing{    
                        pt.clone_data_to_part((depth,i),containing_part, commands);
                    }
                }
            };
        }

        let outer_owners: &HashMap<(usize, usize), Option<usize>> = match sub_adrs{
            Some(v) => {
                &self.subproofs[v].outer
            }
            None => &self.outer
        };
        // Now we will clone the data from outer premises in the respective parts
        for outer_step in outer_premises{
            let outer_owner_address: Option<usize> = *outer_owners.get(&outer_step).unwrap();
            let adjusted_outer_step: (usize, usize) = self.get_new_index_of_outer_premise(sub_adrs, outer_step).unwrap();
            let outer_commands: &Vec<ProofCommand> = self.dive_into_proof(outer_owner_address);
            let containing: Vec<usize> = pt.parts_containing(outer_step).unwrap_or_default();
            for &containing_part in &containing{
                let position = pt.parts[containing_part].part_commands.len();
                pt.clone_data_to_part(adjusted_outer_step, containing_part, outer_commands);

                //Check if some outer step must be collected for each part
                let req: usize = if self.is_premise_of_part_conclusion(containing_part, adjusted_outer_step, &pt){
                    3
                }else{
                    2
                };
                if pt.is_premise_of_resolution(outer_step) &&
                pt.counting_in_part(outer_step, containing_part)>=req &&
                pt.is_resolution_part(containing_part)
                {
                    pt.add_to_units_queue_of_part(outer_step, containing_part, position, &self.subproofs, proof_pool);
                }
                
            }
        }
        pt
    }

    fn fix_broken_proof(&mut self, 
        pt: &mut PartTracker, 
        sub_adrs: Option<usize>, 
        proof_pool: &mut PrimitivePool)
        { //ok
        for p in &mut pt.parts{
            if p.compressible{
                let mut to_recompute: Vec<ReResolveInfo> = vec![];
                let mut global_to_local: HashMap<(usize,usize),usize> = HashMap::new();
                let n = p.part_commands.len();
                let queue = &p.units_queue;
                let mut changed: HashSet<(usize,usize)> = HashSet::new();
                for &q in queue{
                    changed.insert(q);
                }
                for (i, step) in p.part_commands.iter().rev().enumerate(){
                    //println!("original indices {:?}",&p.original_index);
                    let index = p.original_index[n-1-i];
                    
                    global_to_local.insert(index, n-1-i);
                    if p.all_premises_remain(&self.subproofs, step)
                    && p.some_premises_changed(&self.subproofs, step, &mut changed){
                        to_recompute.push(ReResolveInfo{
                            substitute: false,
                            location: n-1-i,
                            index
                        });
                        //println!("Adding {:?} in to_recompute",&step);
                        changed.insert(index);
                    }
                    else if p.single_premise_remains(&self.subproofs, step) &&
                    (step.rule() == "resolution" || step.rule() == "th-resolution") {
                        to_recompute.push(ReResolveInfo{
                            substitute: true,
                            location: n-1-i,
                            index
                        });
                        //println!("Adding {:?} in to_recompute",&step);
                        changed.insert(index);
                    }
                    else if p.some_premises_remains(&self.subproofs, step) && 
                    (step.rule() == "resolution" || step.rule() == "th-resolution"){
                        to_recompute.push(ReResolveInfo{
                            substitute: false,
                            location: n-1-i,
                            index
                        });
                        //println!("Adding {:?} in to_recompute",&step);
                        changed.insert(index);
                    }
                };
                for clause in &to_recompute{
                    if self.get_rule(clause.index, sub_adrs)=="contraction"{
                        self.re_contract(p, clause.location, sub_adrs, &global_to_local); //WARNING maybe add proof pool
                    }/* else if self.get_rule(clause.index, sub_adrs)=="reordering"{
                        self.re_reorder(p, clause.location, sub_adrs, &global_to_local)
                    }*/
                    else if clause.substitute{
                        p.substitute(clause.index, p.remaining_premises(&self.subproofs, clause.location)[0]);
                    } else {
                        /*println!("part {:?}",p.ind);
                        println!("global to local: {:?}",&global_to_local);
                        println!("clause {:?}",&clause);*/
                        let (new_clause, 
                            new_premises, 
                            new_args
                        )  = self.re_resolve(
                                p, 
                                clause.location, 
                                sub_adrs, 
                                &global_to_local, 
                                proof_pool
                            );
                        match &mut p.part_commands[clause.location]{
                            ProofCommand::Assume { .. } => panic!("Assumes don't have args nor premises"),
                            ProofCommand::Step(ps) => {
                                ps.args = new_args;
                                ps.premises = new_premises;
                                ps.clause = new_clause;
                            },
                            ProofCommand::Subproof(_) => panic!("You shouldn't change this from outside of the subproof"),
                        }
                    }
                }
            }
        }
    }


    fn reinsert_collected_clauses(&self, pt: &mut PartTracker, sub_adrs: Option<usize>, proof_pool: &mut PrimitivePool){
        let depth = match sub_adrs{
            Some(v) => self.subproofs[v].depth,
            None => 0,
        };
        let void_proof: Vec<ProofCommand> = vec![];
        let mut cache: Vec<&Vec<ProofCommand>> = vec![&void_proof;depth+1];
        cache[depth] = self.dive_into_proof(sub_adrs);
        // Stores the conclusion on each part and the part index
        let mut conclusions: Vec<(usize,ProofCommand)> = Vec::new();
        for p in & pt.parts{
            let queue = &p.units_queue;
            if p.compressible && !queue.is_empty(){
                let queue_local = &p.queue_local;
                let args_queue = &p.args_queue;
                let mut args: Vec<Rc<Term>> = Vec::new();
                let mut premises: Vec<Premise<'_>>=  Vec::new();
                
                // The part was constructed traversing the proof bottom-up
                // So the 0-th position contains the "root"
                let mut first: &ProofCommand = &p.part_commands[0];
                let location: (usize, usize) = p.original_index[0];
                // Verifies if the conclusion was substituted
                first = p.get_substitute(first, location);
                // Builds and saves in command the data that will be used on resolution
                let command: ProofCommand;
                match &cache[depth][location.1]{
                    ProofCommand::Assume { id, .. } => 
                    command = ProofCommand::Assume{id: id.clone(),
                                                    term: self.command_clause(first)[0].clone() 
                                                    },
                    ProofCommand::Step(ps) => {
                        let mut ps_temp = ps.clone();
                        ps_temp.clause = self.command_clause(first).to_vec();
                        command = ProofCommand::Step(ps_temp);
                    }
                    ProofCommand::Subproof(ph_sp) => {//Warning: subproof as last step of a part
                        let sp = self.access_subproof(ph_sp);
                        let sub_conclusion: &ProofCommand = sp.commands.last().expect("Error: Empty subproof");
                        if let ProofCommand::Step(ps) = sub_conclusion{
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = self.command_clause(first).to_vec();
                            command = ProofCommand::Step(ps_temp);
                        } else {
                            panic!("The last element of a subproof should be a Step");
                        }
                    }
                }
                premises.push(Premise::new(location,&command));
                let mut new_commands: Vec<((usize,usize),ProofCommand)> = Vec::new();
                for (i, location) in queue.iter().enumerate(){
                    let old_location = location;
                    let location: (usize, usize) = self.get_new_index_of_outer_premise(sub_adrs, *old_location).unwrap();
                    let local_ind = queue_local[i];
                    let mut local_step = &p.part_commands[local_ind];
                    local_step = p.get_substitute(local_step, location);
                    let new_comm: ProofCommand;
                    let command_depth: usize = location.0;
                    if cache[command_depth].is_empty(){
                        let new_sub = match command_depth{
                            0 => None,
                            i => Some(i-1)
                        };
                        cache[command_depth] = self.dive_into_proof(new_sub);
                    }
                    match &cache[command_depth][location.1]{
                        ProofCommand::Assume { id, ..} => 
                        new_comm = ProofCommand::Assume{id: id.clone(),
                                                       term: self.command_clause(local_step)[0].clone() 
                                                      },
                        ProofCommand::Step(ps) => {
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = self.command_clause(local_step).to_vec();
                            new_comm = ProofCommand::Step(ps_temp);
                        }
                        ProofCommand::Subproof(sp_ph) => {//Warning: subproof as last step of a part
                                                                    //Should probably be dead code as subproofs introduce new premises
                            let sp = self.access_subproof(sp_ph);
                            let sub_conclusion = &sp.commands.last().expect("Empty subproof");
                            if let ProofCommand::Step(ps) = sub_conclusion{
                                let mut ps_temp = ps.clone();
                                ps_temp.clause = self.command_clause(local_step).to_vec();
                                new_comm = ProofCommand::Step(ps_temp);
                            } else {
                                panic!("The last element of a subproof should be a Step");
                            }
                        }
                    }
                    new_commands.push((location,new_comm));
                }
                for (l,c) in &new_commands{
                    premises.push(Premise::new(*l,c));
                }
                for (lit, polarity) in args_queue{
                    args.push(lit.clone());
                    args.push(polarity.clone());
                }
                //self.enforce_resolution_compatibility(&mut premises, &mut args, proof_pool);
                let resolution: Result<(IndexSet<(u32, &Rc<Term>)>, Vec<usize>), CheckerError> = Self::resolve_when_possible(&premises, &args, proof_pool);
                //let resolution: Result<IndexSet<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<IndexSet<_>>(&premises, &args, proof_pool);
                match resolution{
                    Ok((v, useless))=>{
                        let mut conclusion_prem = vec![];
                        for (i, pr) in premises.iter().enumerate(){
                            if !useless.contains(&i){
                                conclusion_prem.push(pr.index);
                            }
                        }
                        let new_conclusion = ProofCommand::Step(ProofStep{
                            premises: conclusion_prem,
                            id: format!("n{:?}",p.ind),
                            clause: v.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect(),
                            rule: String::from("resolution"),
                            args: vec![],
                            discharge: vec![],
                        });
                        conclusions.push((p.ind,new_conclusion));
                    }
                    
                    Err(_) => panic!("Error: Clauses couldn't be resolved\nReinserting on part {:?}.{:?}\nPremises: {:?}\nArguments: {:?}",
                    depth, p.ind, premises, args),
                }
            }
        }
        for (ind,conc) in conclusions{
            pt.parts[ind].new_conclusion = Some(conc);
            pt.parts[ind].compressed = true;
        }
    }

    fn rebuild(&mut self, pt: &mut PartTracker, sub_adrs: Option<usize>) -> Vec<ProofCommand>{
        let depth: usize = match sub_adrs {
            None => 0,
            Some(v) => self.subproofs[v].depth
        };
        let mut a_count: usize = 0;
        let mut t_count: usize = 0;
        let base_string: String = self.get_base_id(sub_adrs);
        let mut table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
        
        let mut premises: IndexSet<Rc<Term>> = IndexSet::new();
        let mut discharge: Vec<(usize,usize)> = vec![];
        let mut new_commands: Vec<ProofCommand> = vec![];
        
        let assumes: &Vec<ProofCommand> = &pt.parts[0].part_commands;
        let n = assumes.len();
        // Builds the premises field and insert the assumes in the proof
        for (i, a) in assumes.iter().rev().enumerate(){
            let index: (usize, usize) = pt.parts[0].original_index[n-i-1];
            if depth==index.0{
                let com = ProofCommand::Assume {
                    id: format!("{}a{:?}", &base_string, a_count), 
                    term: self.command_clause(a)[0].clone()
                };
                ProofCompressor::insert_command_on_new_proof(
                                            &mut new_commands,
                                                            com,
                                                            &mut table,
                                                            index,
                                                            depth
                                                            );
                a_count+=1;
                discharge.push((depth,i));

            }
            if depth==0{
                premises.insert(self.command_clause(a)[0].clone());
            }
        }
        match sub_adrs {
            None => (),
            Some(v) => self.subproofs[v].discharge = discharge,
        }
        for part in pt.parts[1..].iter().rev(){
            //println!("Marked for deletion on part {:?}: {:?}",part.ind,&part.marked_for_deletion);
            //self.print_part(part);
            //println!("Original indexes: {:?}",&part.original_index);
            for (i, c) in part.part_commands.iter().enumerate().rev(){
                let index = part.original_index[i];
                
                if !(table.contains_key(&index) ||                    // ensures it was not already added in the proof
                    part.marked_for_deletion.contains(&index))&& // ensures it is not substituted
                    index.0==depth
                {
                    let mut com = c.clone();
                    //println!("Command {:?}\n",&com);
                    match &mut com{ //update 
                        ProofCommand::Assume{..} => (),
                        ProofCommand::Step(ps) => {
                            if !self.sp_binder.contains(&ps.rule){
                                self.update_vec(&mut ps.premises, &table, sub_adrs);
                                ps.id = format!("{}t{:?}", &base_string, t_count);
                                t_count+=1;
                            }
                            //println!("ps after {:?}\n",&ps);
                        }
                        ProofCommand::Subproof(sp_ph) => {
                            let id = sp_ph.context_id;
                            self.subproofs[id].new_ind = new_commands.len();
                            //let sp_conclusion = self.subproofs[id].proof.commands.last_mut().unwrap();
                            if let ProofCommand::Step(ps) = sp_ph.commands.last().unwrap(){
                                let mut ps_c = ps.clone();
                                self.update_vec(&mut ps_c.premises, &table, sub_adrs);
                                ps_c.id = format!("{}t{:?}", &base_string, t_count);
                                /*let temp = ps_c.clause.pop();
                                ps_c.clause.reverse();
                                ps_c.clause.push(temp.unwrap());*/
                                //println!("conclusion after {:?}\n",&ps_c);
                                com = ProofCommand::Step(ps_c);
                                t_count+=1;
                            }

                        }
                    }
                    ProofCompressor::insert_command_on_new_proof(
                        &mut new_commands,
                                        com,
                                        &mut table,
                                        index,
                                        depth
                                    );
                }
            }
            let conclusion: Option<ProofCommand> = part.new_conclusion.clone();
            //println!("conclusion {:?}",&conclusion);
            match conclusion{
                None => (),
                Some(ProofCommand::Step(mut ps)) => {
                    self.update_vec(&mut ps.premises, &table, sub_adrs);
                    ps.id = format!("{}t{:?}", &base_string, t_count);
                    t_count+=1;
                    new_commands.push(ProofCommand::Step(ps));
                },
                _ => panic!("Sim"),
            }
        }
        self.fill_fixed(table,sub_adrs);
        new_commands
    }

    fn update_vec(&self, v: &mut [(usize,usize)], table: &HashMap<(usize,usize),(usize,usize)>, sub_adrs: Option<usize>){
        for prem in v.iter_mut() {
            if let Some(updt_prem) = table.get(prem) {
                *prem = *updt_prem;
            } else { //if prem is not in the table, then it must be an outer premise
                *prem = self.get_new_index_of_outer_premise(sub_adrs, *prem).unwrap();
            }
        }
    }

    fn fill_fixed(&mut self, table: HashMap<(usize,usize),(usize,usize)>, sub_adrs: Option<usize>){
        let fixed: &mut HashMap<(usize, usize), Option<(usize, usize)>> = match sub_adrs{
            None => &mut self.fixed,
            Some(v) => &mut self.subproofs[v].fixed,
        };
        for (old_ind, destination) in fixed.iter_mut() {
            let new_ind: (usize, usize) = *table.get(old_ind).unwrap();
            *destination = Some(new_ind);
        }
    }

    fn update_id(v: &mut Vec<(usize,usize)>, table: &HashMap<(usize,usize),(usize,usize)>){
        for prem in v.iter_mut() {
            if let Some(updt_prem) = table.get(prem) {
                *prem = *updt_prem;
            }
        }
    }

    fn get_new_index_of_outer_premise(&self, sub_adrs: Option<usize>, old_ind: (usize,usize))->Option<(usize,usize)>{
        let outer = match sub_adrs{
            None => &self.outer,
            Some(v) => &self.subproofs[v].outer,
        };

        match outer.get(&old_ind){
            Some(None) => self.fixed[&old_ind],
            Some(Some(v)) => self.subproofs[*v].fixed[&old_ind],
            None => Some(old_ind)
        }
    }

    fn insert_command_on_new_proof(
        new_proof: &mut Vec<ProofCommand>, 
        com: ProofCommand, 
        table: &mut HashMap<(usize,usize),(usize,usize)>,
        index: (usize,usize), 
        depth: usize
    ){
        
        let n = new_proof.len();
        //println!("N: {n}");
        table.insert(index,(depth,n));
        //println!("Command {:?} is being tabled",&com);
        new_proof.push(com);
        //println!("{:?} to {:?} being inserted",index,(depth,n));
    }

    fn command_rule<'b>(&'b self,pc: &'b ProofCommand) -> &'b str{
        match pc {
            ProofCommand::Assume {..} => "assume",
            ProofCommand::Step(s) => &s.rule,
            ProofCommand::Subproof(ssp) => {
                if let ProofCommand::Step(ps) = &ssp.commands[0]{
                    &ps.rule
                } else {
                    panic!("The last element of a subproof should be a proof step")
                }
            },
        }
    }

    fn command_premises<'b>(&'b self,pc: &'b ProofCommand) -> &'b Vec<(usize,usize)>{
        match pc {
            ProofCommand::Assume {..} => {
                static NO_PREM: Vec<(usize,usize)> = Vec::new();
                &NO_PREM
            },
            ProofCommand::Step(s) => &s.premises,
            ProofCommand::Subproof(ssp) => {
                if let ProofCommand::Step(ps) = &ssp.commands[0]{
                    &ps.premises
                } else {
                    panic!("The last element of a subproof should be a proof step")
                }
            },
        }
    }

    fn command_args<'b>(&'b self,pc: &'b ProofCommand) -> &'b Vec<Rc<Term>>{
        match pc {
            ProofCommand::Assume {..} => {
                static NO_ARGS: Vec<Rc<Term>> = Vec::new();
                &NO_ARGS
            },
            ProofCommand::Step(s) => &s.args,
            ProofCommand::Subproof(ssp) => {
                if let ProofCommand::Step(ps) = &ssp.commands[0]{
                    &ps.args
                } else {
                    panic!("The last element of a subproof should be a proof step")
                }
            },
        }
    }

    fn plc_hodr_or_command_id<'b>(&'b self,pc: &'b ProofCommand) -> &'b str{
        match pc {
            ProofCommand::Assume {id,..} => id,
            ProofCommand::Step(s) => &s.id,
            ProofCommand::Subproof(ssp) => {
                if let ProofCommand::Step(ps) = &ssp.commands[0]{
                    &ps.id
                } else {
                    println!("sp {:?}",ssp);
                    panic!("The last element of a subproof should be a proof step")
                }
            },
        }
    }
   
    fn command_clause<'b>(&'b self,pc: &'b ProofCommand) ->  &'b [Rc<Term>]{
        match pc {
            ProofCommand::Assume {term,..} => std::slice::from_ref(term),
            ProofCommand::Step(s) => &s.clause,
            ProofCommand::Subproof(ssp) => {
                if let ProofCommand::Step(ps) = &ssp.commands[0]{
                    &ps.clause
                } else {
                    panic!("The last element of a subproof should be a proof step")
                }
            },
        }
    }

    fn get_rule(&self, step: (usize, usize), sub_adrs: Option<usize>) -> &str{ //ok
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => "assume",
            Some(ProofCommand::Step(ps)) => &ps.rule,
            Some(ProofCommand::Subproof(ssp)) => {
                let sp = self.access_subproof(&ssp);
                if let ProofCommand::Step(ps) = sp.commands.last().expect("A subproof shouldn't be empty"){
                    &ps.rule
                } else {
                    panic!("last step of a subproof should be a proof step")
                }
            }
            None => panic!("Index out of bounds for the command vector")
        }
    }
    

    fn get_clause_len(&self, step: (usize, usize), sub_adrs: Option<usize>) -> usize{ //ok
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => 1,
            Some(ProofCommand::Step(ps)) => ps.clause.len(),
            Some(ProofCommand::Subproof(ssp)) => {
                let sp = self.access_subproof(&ssp);
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => sub_ps.clause.len(),
                    Some(_) => panic!("The last step of a subproof should be a step"),
                    None => panic!("This subproof shouldn't be empty")
                }
            }
            None => panic!("Index out of bound for the command vector")
        }
    }

    fn position_insert(&mut self, mut new_commands: Vec<ProofCommand>, sub_adrs: Option<usize>){
        match sub_adrs{
            None => self.proof.commands = new_commands,
            Some(i) => self.subproofs[i].proof.commands = new_commands
        }
    }

    fn get_base_id(&self, sub_adrs: Option<usize>) -> String{
        match sub_adrs{
            None => String::from(""),
            Some(i) => {
                let current_sub: &SubproofMeta = &self.subproofs[i]; 
                let ind = current_sub.new_ind;
                let super_proof = self.dive_into_proof(current_sub.parent_adrs);
                let mut base = String::from(super_proof[ind].id());
                if !base.is_empty(){
                    base += ".";
                }
                base
            }
        }
    }

    fn step_is_resolution(&self, step: (usize, usize), sub_adrs: Option<usize>) -> bool{ //ok
        let ind = step.1;
        let commands: &Vec<ProofCommand>;
        let adrs_depth = match sub_adrs{
            Some(v) => self.subproofs[v].depth,
            None => 0
        };
        if step.0 == 0{
            commands = &self.proof.commands;
        } else if adrs_depth == step.0{
            commands = self.dive_into_proof(sub_adrs);
        } else {
            let owner = self.fetch_owner_subproof(sub_adrs, step.0).unwrap();
            commands = &self.subproofs[owner].proof.commands;
        }
        match commands.get(ind){
            Some(ProofCommand::Step(ps)) => ps.rule=="resolution" || ps.rule =="th-resolution",
            Some(_) => false,
            None => panic!("This command doesn't exist")
        }
    }
    
    fn resolution_is_a_premise(&self, step: &ProofStep, sub_adrs: Option<usize>) -> bool{ //ok
        if step.premises.len()==1{
            let (depth, ind) = step.premises[0];
            let commands = match sub_adrs{
                None => &self.proof.commands,
                Some(v) => {
                    if depth==self.subproofs[v].depth{
                        &self.subproofs[v].proof.commands
                    } else {
                        &self.subproofs[self.fetch_owner_subproof(sub_adrs, depth).unwrap()].proof.commands
                    }
                }
            };
            let rule = self.command_rule(&commands[ind]);
            rule == "resolution" || rule == "th-resolution"
        } else {
            panic!("reorder or contract with more than one premise")
        }
    }
    
    fn get_current_fix(&self, sub_adrs: Option<usize>) -> &HashMap<(usize,usize),Option<(usize,usize)>>{
        match sub_adrs{
            None => &self.fixed,
            Some(v) => &self.subproofs[v].fixed,
        }
    }

    fn get_current_outer(&self, sub_adrs: Option<usize>) -> &HashMap<(usize,usize),Option<usize>>{
        match sub_adrs{
            None => &self.outer,
            Some(v) => &self.subproofs[v].outer,
        }
    }

    
    fn re_contract(&mut self, 
        part: &mut DisjointPart, 
        index: usize, 
        sub_adrs: Option<usize>,
        global_to_local: &HashMap<(usize,usize),usize>
    ){ // ok
        let sp_stack = &self.subproofs;
        if let Some(premises) = part.part_commands[index].premises(sp_stack){
            let parent_global_ind = premises[0];
            let op_local_ind = global_to_local.get(&parent_global_ind);
            match op_local_ind{
                Some(parent_local_ind) => {
                    let parent_clause: Vec<Rc<Term>> = 
                        self
                        .command_clause(&part.part_commands[*parent_local_ind])
                        .to_vec();
                    let clause_set: IndexSet<Rc<Term>> = parent_clause.into_iter().collect();
                    let new_contract: Vec<Rc<Term>> = clause_set.into_iter().collect();
                    let to_compress = &mut part.part_commands[index];
                    self.overwrite_clause(to_compress, new_contract);
                }
                None => panic!("This clause wasn't mapped in global_to_local")
            }
        }
    }

    fn overwrite_clause(&mut self, to_overwrite: &mut ProofCommand, new_clause: Vec<Rc<Term>>){ // ok
        match to_overwrite{
            ProofCommand::Assume {term ,..} => {
                if new_clause.len()>1 {
                    panic!("Trying to insert not-unary clause into an assertion")
                } else if new_clause.is_empty() {
                    panic!("Trying to insert empty clause into an assertion")
                }
                *term = new_clause[0].clone();
            }
            ProofCommand::Step(ps) => {
                ps.clause = new_clause;
            }
            ProofCommand::Subproof(sp_ph) => {
                let sp = self.access_subproof_mut(sp_ph);
                if let ProofCommand::Step(sps) = sp.commands.last_mut().unwrap(){
                    sps.clause = new_clause;
                }
            }
        }
    }
    
    fn re_resolve(&self, 
        part: &mut DisjointPart, 
        index: usize, 
        sub_adrs: Option<usize>, 
        global_to_local: &HashMap<(usize,usize),usize>,
        proof_pool: &mut PrimitivePool,
    ) -> 
    (Vec<Rc<Term>>,Vec<(usize,usize)>,Vec<Rc<Term>>){
        let sp_stack: &Vec<SubproofMeta> = &self.subproofs;
        let mut remaining: Vec<(usize, usize)> = part.remaining_premises(sp_stack, index);
        //println!("Remaining {:?}",&remaining);
        let table: &HashMap<(usize, usize), (usize, usize)> = &part.subs_table;
        //println!("table: {:?}",table);
        //println!("\nglobal to local: {:?}",&global_to_local);
        let mut new_commands: Vec<(ProofCommand,(usize,usize))> = Vec::new();
        let mut premises: Vec<Premise<'_>> = self.build_premises(part, &remaining, global_to_local, index, sub_adrs, &mut new_commands);
        //println!("\nPremises: {:?}",&premises);
        let args = self.build_args(part, &remaining, index);
        //println!("Args: {:?}", &args);
        // substituting premises
        for r in &mut remaining{
            if let Some(rr) = table.get(r) {
                let aft_subs = self.get_new_index_of_outer_premise(sub_adrs, *rr).unwrap();
                for p in &mut premises{
                    if p.index==*r{        
                        p.index = aft_subs;
                        let local_ind: usize = *global_to_local.get(&aft_subs).unwrap();
                        p.clause = self.command_clause(&part.part_commands[local_ind]);
                    }
                 }
                 *r = aft_subs;
             }
        }
        if part.is_behaved(index){      // This step will be contracted or reordered in future, 
                                                    // so here the result will be a vector to avoid contracting it now
            let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<Vec<_>>(&premises, &args, proof_pool);
            match resolution{
                Ok(r) => {
                    let resolvent: Vec<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                    let formatted_premises = premises.iter().map(|x| x.index).collect();
                    (resolvent, formatted_premises, vec![])
                }
                _ => panic!("Error: Clauses couldn't be resolved\n
                        Resolving for {:?} on part {:?}\n
                        Premises: {:?}\n
                        Arguments: {:?}", 
                        index, part.ind, premises, args),
            }
        } else {
            let resolution: Result<IndexSet<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<IndexSet<_>>(&premises, &args, proof_pool);
            match resolution{
                Ok(r) => {
                    let resolvent_set: IndexSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();    
                    let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                    let formatted_premises = premises.iter().map(|x| x.index).collect();
                    /*step.clause = resolvent;
                    step.args = args;*/
                    (resolvent, formatted_premises, args)
                }
                _ => panic!("Error: Clauses couldn't be resolved\n
                        Resolving for {:?} on part {:?}\n
                        Premises: {:?}\n
                        Arguments: {:?}", 
                        index, part.ind, premises, args),
            }
        }
    }

    fn build_premises(&'a self,
        part: &DisjointPart, 
        remaining: &[(usize, usize)], 
        global_to_local: &HashMap<(usize,usize),usize>, 
        index: usize, 
        sub_adrs: Option<usize>, 
        new_commands: &'a mut Vec<(ProofCommand,(usize,usize))>
    ) -> Vec<Premise<'a>>{ // ok
        let depth = match sub_adrs{
            Some(v) => self.subproofs[v].depth,
            None => 0,
        };
        let sp_stack: &Vec<SubproofMeta> = &self.subproofs;
        let void_proof: Vec<ProofCommand> = vec![];
        let mut cache: Vec<&Vec<ProofCommand>> = vec![&void_proof;depth+1];
        cache[depth] = self.dive_into_proof(sub_adrs);
        let mut ans: Vec<Premise> = vec![];
        let data = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().copied().collect();
        
        let op_prem: Option<&Vec<(usize, usize)>> = data.premises(sp_stack);
        if let Some(prem) = op_prem{
            for p in prem{
                if remaining_set.contains(p){
                    let new_comm: ProofCommand;
                    if cache[p.0].is_empty(){
                        let new_sub = match p.0{
                            0 => None,
                            i => Some(i-1)
                        };
                        cache[p.0] = self.dive_into_proof(new_sub);
                        //cache[p.0] = self.dive_into_proof(&sub_adrs[0..p.0]);
                    }
                    let local: usize = *global_to_local.get(p).unwrap();
                    let local_step = &part.part_commands[local];
                    match &cache[p.0][p.1]{
                        ProofCommand::Assume { id, .. } => 
                        new_comm = ProofCommand::Assume{id: id.clone(),
                                                        term: self.command_clause(local_step)[0].clone() 
                                                        },
                        ProofCommand::Step(ps) => {
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = self.command_clause(local_step).to_vec();
                            new_comm = ProofCommand::Step(ps_temp);
                        }
                        ProofCommand::Subproof(ph_sp) => {
                            let sp = self.access_subproof(ph_sp);
                            let sub_conclusion = sp.commands.last().unwrap();
                            if let ProofCommand::Step(ps) = sub_conclusion{
                                let mut ps_temp = ps.clone();
                                ps_temp.clause = self.command_clause(local_step).to_vec();
                                new_comm = ProofCommand::Step(ps_temp);
                            } else {
                                panic!("The last element of a subproof should be a Step");
                            }
                        }
                    }
                    new_commands.push((new_comm,*p));
                }
            }
        }
        for (c,loc) in new_commands.iter(){
            ans.push(Premise::new(*loc,c));
        }
        ans
    }    

    fn build_args(&self, part: &DisjointPart, remaining: &[(usize, usize)], index: usize) -> Vec<Rc<Term>>{ // ok
        let mut ans: Vec<Rc<Term>> = vec![];
        let sp_stack = &self.subproofs;
        let data = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().copied().collect();
        let old_args = self.command_args(data); 
        if let Some(premises) = data.premises(sp_stack){
            let n: usize = if remaining_set.contains(&premises[0]) {1} else {2};
            for (i, &p) in premises.iter().enumerate().skip(n){
                if remaining_set.contains(&p){
                    ans.push(old_args[2*i-2].clone());
                    ans.push(old_args[2*i-1].clone());
                }
            }
        }
        ans
    }
    
    pub fn access_subproof(&self, placeholder: &Subproof) -> &Subproof{ //ok
        &self.subproofs[placeholder.context_id].proof
    }

    pub fn access_subproof_mut(&mut self, placeholder: &Subproof) -> &mut Subproof{ //ok
        &mut self.subproofs[placeholder.context_id].proof
    }

    fn must_be_a_new_conclusion(&self, step: (usize, usize), pt: &PartTracker, sub_adrs: Option<usize>)->bool{ //ok
        let fixed = match sub_adrs{
                                                    Some(v) => &self.subproofs[v].fixed,
                                                    None => &self.fixed
                                                };
        !pt.is_conclusion.contains(&step) && fixed.contains_key(&step)
    }

    fn single_assume_is_premise(&self, step: (usize, usize), commands: &Vec<ProofCommand> ,sub_adrs: Option<usize>) -> bool{
        match &commands[step.1]{
            ProofCommand::Step(ps) => {
                if ps.premises.len()==1{
                    let prem = ps.premises[0];
                    if prem.0==step.0{
                        commands[prem.1].is_assume()
                    } else if prem.0==0{
                        self.proof.commands[prem.1].is_assume()
                    } else {
                        let ind = self.fetch_owner_subproof(sub_adrs, prem.0).unwrap();
                        self.subproofs[ind].proof.commands[prem.1].is_assume()
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_premise_of_part_conclusion(&self, part_ind: usize, index: (usize,usize), pt: &PartTracker) -> bool{
        let part = &pt.parts[part_ind];
        match &part.part_commands[0]{
            ProofCommand::Assume{..} => false,
            ProofCommand::Step(ps) => ps.premises.contains(&index),
            ProofCommand::Subproof(sp_ph) => {
                let sp = self.access_subproof(sp_ph);
                if let ProofCommand::Step(ps) = sp.commands.last().unwrap(){
                    ps.premises.contains(&index)
                } else {
                    panic!("Every subproof should end in a ProofStep")
                }
            }
        }
    }

    fn reassemble(&mut self){
        let n: usize = self.subproofs.len();
        let mut subproof_meta: Vec<SubproofMeta> = mem::take(&mut self.subproofs);
        for sub_ind in (0..n).rev(){
            let parent_adrs: Option<usize> = subproof_meta[sub_ind].parent_adrs;
            let new_ind: usize = subproof_meta[sub_ind].new_ind;
            let meta: SubproofMeta = subproof_meta.pop().unwrap();
            let discharge: Vec<(usize, usize)> = meta.discharge;
            let mut sub: Subproof = meta.proof;
            if let ProofCommand::Step(ps) = sub.commands.last_mut().unwrap(){
                ps.discharge = discharge;
            }
            let commands: &mut Vec<ProofCommand> = match parent_adrs{
                None => &mut self.proof.commands,
                Some(v) => &mut subproof_meta[v].proof.commands,
            };

            // The step with the subproof conclusion had was adjusted at the parent level
            // I.e., the subproof at depth 3 was adjusted while running the algorithm at level 2
            // This operation puts the adjusted conclusion
            mem::swap(&mut commands[new_ind], sub.commands.last_mut().unwrap());
            commands[new_ind] = ProofCommand::Subproof(sub);
        }
    }

    fn dive_into_proof(&self, sub_adrs: Option<usize>) -> &Vec<ProofCommand>{ //ok
        match sub_adrs{
            None => &self.proof.commands,
            Some(i) => &self.subproofs[i].proof.commands
        }
    }

    fn dive_into_proof_mut(&mut self, sub_adrs: Option<usize>) -> &mut Vec<ProofCommand>{ //ok
        match sub_adrs{
            None => &mut self.proof.commands,
            Some(i) => &mut self.subproofs[i].proof.commands
        }
    }

    fn print_part(&self, part: &DisjointPart){
        println!("Part {:?}", part.ind);
        for (i, com) in part.part_commands.iter().enumerate(){
            match com{
                ProofCommand::Assume { id, term } => println!("{:?} - Assume {:?}: {:?}; {:?}",i,id,term,part.original_index[i]),
                ProofCommand::Step(ps) => 
                println!("{:?} - Step {:?} {:?}: {:?}; prem: {:?}; arg: {:?}; {:?}",i,&ps.id,&ps.rule,&ps.clause,&ps.premises, &ps.args, part.original_index[i]),
                ProofCommand::Subproof(sp_ph) => {
                    let sp = self.access_subproof(&sp_ph);
                    match sp.commands.last(){
                        None => panic!("empty"),
                        Some(ProofCommand::Step(ps)) => println!("{:?} - Sub {:?} {:?}: {:?}; prem: {:?}; disc: {:?}; {:?}",i,&ps.id,&ps.rule,&ps.clause,&ps.premises, &ps.discharge, part.original_index[i]),
                        _ => panic!("Not a proofstep")
                    };
                }
            }
        }
    }

    /*fn pivot_will_be_used(premise: &Premise, pivot: (u32, &Rc<Term>), polarity: bool) -> bool{
        let mut found = false;
        let term = literal_to_term()
        if polarity {
            for cl in premise.clause.iter(){
                if cl.remove_all_negations().0 == *pivot{
                    found = true;
                }
            }
        }
        
        found
    }*/

    fn resolve_when_possible( 
        premises: &Vec<Premise<'a>>, 
        mut args: &'a Vec<Rc<Term>>, 
        pool: &mut PrimitivePool
    ) -> Result<(IndexSet<(u32, &'a Rc<Term>)>,Vec<usize>), CheckerError>{
        let num_steps = premises.len() - 1;
        let args: Vec<_> = args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].remove_all_negations();
            let polarity = chunk[1].clone();
            let polarity = if polarity.is_bool_true() {
                true
            } else if polarity.is_bool_false() {
                false
            } else {
                return Err(CheckerError::ExpectedAnyBoolConstant(polarity.clone()));
            };
            Ok((pivot, polarity))
        })
        .collect::<Result<_, _>>()?;
        let mut useless_premise: Vec<usize> = vec![];
        let mut current:IndexSet<(u32, &Rc<Term>)>  = premises[0]
        .clause
        .iter()
        .map(Rc::remove_all_negations)
        .collect();
        for (i, (premise, (pivot, polarity))) in premises[1..].iter().zip(args).enumerate() {
            let result = binary_resolution(pool, &mut current, premise.clause, pivot, polarity);
            match result {
                Err(_) => {
                    useless_premise.push(i+1);
                }
                Ok(()) => ()
            };
        }
        Ok((current, useless_premise))
        //Err(CheckerError::DivOrModByZero)
    }

    /*fn enforce_resolution_compatibility(&self, mut premises: &mut Vec<Premise<'_>>, mut args: &mut Vec<Rc<Term>>, pool: &mut PrimitivePool){
        let mut aux: usize = 1;
        let mut redundant: Vec<usize> = Vec::new();
        for arg in args.chunks(2){
            let term: &Rc<Term> = &arg[0];
            let polarity: &Rc<Term> = &arg[1];
            if Term::Op(Operator::True, Vec::new()) == (**polarity).clone(){ //look for term
                if !premises[0].clause.contains(term){
                    redundant.push(aux)
                }
            } else { //look for not term
                let unwr_term = (**term).clone();
                let mut found = false;
                for cl in premises[0].clause{
                    match cl.remove_negation(){
                        None => (),
                        Some(t) => {
                            if &((**t).clone())==&unwr_term{
                                found = true;
                            }
                        }
                    }
                }
                if !found{
                    redundant.push(aux);
                }
            }
            aux+=1;
        }
        premises = premises.iter()
            .enumerate()
            .filter(|(i, _)| !redundant.contains(i))
            .map(|(_, &val)| val)
            .collect();

        args = args.iter()
            .enumerate()
            .filter(|(i, _)|)

    }*/
    //fn map_to_new_loc(&self, outer_step: OuterPremiseAdrs) -> usize{}
}

fn print_proof(p: &Vec<ProofCommand>, indentation: String, base: usize, depth: usize) -> usize{
    let mut from = base;
    let mut sub_len: usize = 0;
    let it: Box<dyn Iterator<Item = (usize, &ProofCommand)>> = if depth == 0 {
        Box::new(p.iter().enumerate())
    } else {
        Box::new(p.iter().enumerate().take(p.len() - 1))
    };
    for (i, c) in it{
        match c{
            ProofCommand::Assume { id, term } => println!("{}{} - {} Assume: {}; ({},{})", &indentation, i+from, id, term, depth, i),
            ProofCommand::Step(ps) => {
                let mut s: String = format!("{}{} - {} {}: {:?}", &indentation, from+i, &ps.id, &ps.rule, &ps.clause).to_string();
                if !ps.premises.is_empty(){
                    let prem = format!(", premises: {:?}", &ps.premises);
                    s = s + &prem;
                }
                if !ps.args.is_empty(){
                    let args = format!(", args: {:?}", &ps.args);
                    s = s + &args;
                }
                if !ps.discharge.is_empty(){
                    let disc = format!(", discharge: {:?}", &ps.discharge);
                    s = s + &disc;
                }
                let addrs = format!("; ({:?},{:?})", depth, i);
                s = s + &addrs;
                println!("{}",s);
            }
            ProofCommand::Subproof(sp) => {
                let mut op = format!("{}Opening subproof, id: {}, args: {:?}", &indentation, &sp.context_id, &sp.args);
                println!("{:?}",&op);
                let new_indentation = indentation.clone() + "   ";
                sub_len = print_proof(&sp.commands, new_indentation, i+from, depth+1);
                from += sub_len;
                match sp.commands.last(){
                    None => panic!("Empty subproof at printer"),
                    Some(ProofCommand::Step(ps)) => {
                        let mut s: String = format!("{}{} - {} {}: {:?}", &indentation, from+i, &ps.id, &ps.rule, &ps.clause).to_string();
                        if !ps.premises.is_empty(){
                            let prem = format!(", premises: {:?}", &ps.premises);
                            s = s + &prem;
                        }
                        if !ps.args.is_empty(){
                            let args = format!(", args: {:?}", &ps.args);
                            s = s + &args;
                        }
                        if !ps.discharge.is_empty(){
                            let disc = format!(", discharge: {:?}", &ps.discharge);
                            s = s + &disc;
                        }
                        
                        let addrs = format!("; ({:?},{:?})", depth, i);
                        s = s + &addrs;
                        println!("{}",s);
                    }
                    _ => panic!("Subproof not ending in step")
                }
            }
        }
    }
    p.len()+sub_len-1
}

