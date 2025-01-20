//Question: outer_premises that aren't resolution can be thrown out after cloning their data to the parts?
//Only steps that are resolution and are premise of another resolution are compressed by lower units
//benchmarks/small/SH_problems_all_filtered/Green_veriT/x2020_07_28_19_01_13_405_7253502.smt2 rodando ~/carcara/wt-atila/target/release/carcara check -i --allow-int-real-subtyping --expand-let-bindings test.alethe x2020_07_28_19_01_13_405_7253502.smt2

mod tracker;
mod disjoints;
mod error;
use crate::ast::term::Term;
use crate::checker::rules::Premise;
use crate::compressor::error::*;
use crate::ast::proof::*;
use crate::ast::node::*;
use crate::ast::pool::PrimitivePool;
//use crate::ast::node::*;
use std::collections::{HashSet, HashMap};
use std::{mem, vec};
//use std::ops::Index;
//use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
use crate::ast::rc::Rc;
use disjoints::*;
use indexmap::IndexSet;
use std::env;
//use std::env;
use tracker::*;

fn incr(x: Option<usize>) -> Option<usize>{
    match x{
        Some(v) => Some(v+1),
        None => Some(0)
    }
}

fn correct_index(ind: usize, limit: usize) -> usize{
    limit-1-ind
}

fn print_proof(p: &Vec<ProofCommand>, indentation: String, base: usize, depth: usize) -> usize{
    let mut from = base;
    let mut sub_len: usize = 0;
    let it: Box<dyn Iterator<Item = (usize, &ProofCommand)>>;
    if depth == 0 {
        it = Box::new(p.iter().enumerate());
    } else {
        it = Box::new(p.iter().enumerate().take(p.len() - 1));
    }
    for (i, c) in it{
        match c{
            ProofCommand::Assume { id, term } => println!("{}{} - {} Assume: {}; ({},{})", &indentation, i+from, id, term, depth, i),
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
                let addrs = format!("; ({:?},{:?})", depth, i);
                s = s + &addrs;
                println!("{}",s);
            }
            ProofCommand::Subproof(sp) => {
                let new_indentation = indentation.clone() + "   ";
                //println!("i: {i}, from: {from}");
                sub_len = print_proof(&sp.commands, new_indentation, i+from, depth+1);
                from += sub_len;
                match sp.commands.last(){
                    None => panic!("Empty subproof at printer"),
                    Some(ProofCommand::Step(ps)) => {
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

#[derive(Debug)]
pub struct ProofCompressor{
    proof: Proof,
    sp_binder: HashSet<String>, //list of rules that implie that a step opens a subproof
    preserving_binder: HashSet<String>, //list of rules that don't break a disjoint part of resolutions
    subproofs: Vec<SubproofMeta>, //subproofs of the proof with the clauses from them that must not be deleted
    fixed_clauses: HashSet<(usize, usize)>, //clauses from the level 0 used as premise in subproofs
    outer: HashSet<OuterPremiseAdrs>, //deeper dependencies of the level 0 proof
    //sp_count: Option<usize>,
    //stack: Vec<usize>,
    //later_subs_table: HashMap<OuterPremiseAdrs,Vec<OuterPremiseAdrs>>, //Holds the steps used as premises in subproofs and steps that use them 
    new_indexes: HashMap<OuterPremiseAdrs,Option<(usize,usize)>>, //Holds the position of an step after compression 
    //sub_holes: HashMap<usize, OuterPremiseAdrs>,
    /*address_to_pos_id: HashMap<Vec<usize>,Vec<usize>>,
    positional_adrs_to_sp: HashMap<Vec<usize>,usize>,*/
    // non_breaking_rules: HashSet<&'static str>,    //rules that don't break a resolution only disjoint part
}

#[derive(Debug)]
struct SubproofMeta{
    proof: Subproof,
    fixed: HashSet<(usize,usize)>,
    depth: usize,
    outer: HashSet<OuterPremiseAdrs>,
}

#[derive(Debug)]
struct ReResolveInfo{
    substitute: bool,
    location: usize,
    index: (usize, usize),
}

 #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct OuterPremiseAdrs{
    index: (usize, usize),
    sp: Option<usize>
}


impl<'a> ProofCompressor{
    pub fn from(p: Proof)->Self{
        Self{
            proof: p,
            sp_binder: HashSet::from_iter(
                vec![
                    "subproof".to_string(),
                    "let".to_string(),
                    "sko_ex".to_string(),
                    "sko_forall".to_string(),
                    "bind".to_string(),
                    "onepoint".to_string()
                ].into_iter()),
            preserving_binder: HashSet::from_iter(
                vec![
                    "contraction".to_string(),
                    "reordering".to_string()
                ].into_iter()),
            subproofs: Vec::new(),
            fixed_clauses: HashSet::new(),
            outer: HashSet::new(),
            //sp_count: None,
            //stack: Vec::new(),
            //later_subs_table: HashMap::new(),
            new_indexes: HashMap::new(),
            //sub_holes: HashMap::new(),
            /*address_to_pos_id: HashMap::new(),
            positional_adrs_to_sp: HashMap::new(),*/
        }
    }


    pub fn compress_proof(mut self, proof_pool: &mut PrimitivePool) -> Proof{
        env::set_var("RUST_BACKTRACE", "1");
        //print_proof(&self.proof.commands, "".to_string(), 0, 0);
        let _ = &mut self.lower_units(None, 0, proof_pool);
        mem::take(&mut self.proof)
    }

    fn lower_units(&mut self, sub_adrs: Option<usize>, debug_aux: usize, proof_pool: &mut PrimitivePool) -> Result<(), ()> {
        self.get_fixed_clauses(sub_adrs, debug_aux);
        let mut pt: PartTracker = self.collect_units(sub_adrs, debug_aux, proof_pool);
        
        /*for part in pt.parts.iter(){
            self.print_part(part);
        }*/


        //let proof = mem::take(&mut self.proof);
        //let proof_node = ProofNode::from_commands(commands);
        
        self.fix_broken_proof(&mut pt, sub_adrs, debug_aux, proof_pool);
        //self.reinsert_collected_clauses(&mut pt, sub_adrs, proof_pool);
        //self.rebuild(&mut pt, sub_adrs);
        Ok(())
    }

    fn fetch_owner_subproof(&self, sub_adrs: Option<usize>, tgt: usize) -> usize{ //ok //Change
        if tgt==0{
            panic!("Only fetches subproof, this target is the level 0");
        }
        match sub_adrs{
            None => panic!("This is a step from the level 0. There's no superproof of higher level"),
            Some(v) => {
                let mut candidate = v-1;
                loop{
                    if self.subproofs[candidate].depth == tgt{
                        return candidate;
                    }
                    candidate-=1;
                }
            }
        }
    }

    fn get_fixed_clauses(&mut self, sub_adrs: Option<usize>, debug_aux: usize){ //ok
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
                    for &prem in ps.premises.iter(){
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
        for &prem in fixed_clauses.iter(){ //set the clauses as fixed
            if prem.0==0{
                self.fixed_clauses.insert(prem);
                //self.outer.insert(to_insert);
            } else {
                let owner: usize = self.fetch_owner_subproof(sub_adrs, prem.0);
                self.subproofs[owner].fixed.insert(prem);
                let me = match sub_adrs{
                    None => panic!("Dead code, i hope"),
                    Some(v) => v
                };
                self.subproofs[me].outer.insert(OuterPremiseAdrs{
                    index: prem,
                    sp: Some(owner)
                });
            }
        }
        

        for i in subproof_indexes.into_iter(){ //send subproofs to self.subproofs and calls function recursively on them
            let ph = Subproof::new_placeholder(self.subproofs.len());
            let extracted_sp: Subproof;
            {
                let m_commands: &mut Vec<ProofCommand> = self.dive_into_proof_mut(sub_adrs);
                if let ProofCommand::Subproof(sp) = &mut m_commands[i]{
                    extracted_sp = mem::replace(sp,ph);
                } else {
                    panic!("This should be a subproof");
                }
            }
            self.subproofs.push(
                SubproofMeta{
                    proof: extracted_sp,
                    fixed: HashSet::new(),
                    depth: depth+1,
                    outer: HashSet::new(),
                }
            );
            self.get_fixed_clauses(Some(self.subproofs.len()-1), debug_aux);
        }
        //println!("{:?}",fixed_clauses);
    }

    fn collect_units(&mut self, sub_adrs: Option<usize>, debug_aux: usize, proof_pool: &mut PrimitivePool) -> PartTracker{
        let depth: usize;
        let fixed_clauses: &HashSet<(usize,usize)>;
        let outer_clauses: &HashSet<OuterPremiseAdrs>;
        match sub_adrs{
            Some(v) => {
                depth = self.subproofs[v].depth;
                fixed_clauses = &self.subproofs[v].fixed;
                outer_clauses = &self.subproofs[v].outer;
            }
            None => {
                depth = 0;
                fixed_clauses = &self.fixed_clauses;
                outer_clauses = &self.outer;
            }
        };
        println!("Fixed clauses: {:?}", &fixed_clauses);
        //let mut later_subs_table: HashMap<OuterPremiseAdrs,Vec<OuterPremiseAdrs>> = HashMap::new();
        //let mut new_indexes: HashMap<OuterPremiseAdrs,Option<(usize,usize)>> = HashMap::new();
        //let (subproof_to_outer_premises, outer_premises) = self.process_subproofs(sub_adrs, debug_aux+1, proof_pool);        
        //let mut outer_premises: IndexSet<OuterPremiseAdrs> = outer_premises.iter().filter( |&&x | x.index.0<depth).cloned().collect();
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        let n = commands.len();
        let mut pt = PartTracker::new(self.step_is_resolution((depth,n-1), sub_adrs), depth);
        /*for prem in fixed_clauses{
            pt.set_cant_be_deleted(prem); // Prohibits the compression algorithm from deleting steps that are used as premises in subproofs
        }*/
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
                    for &containing_part in &containing{
                        let position = pt.parts[containing_part].part_commands.len();
                        // The data in the Assume should be added to the DisjointParts of the Tracker
                        pt.clone_data_to_part((depth,i),containing_part, commands);

                        // Check if this step must be collected in this part
                        if pt.is_premise_of_resolution((depth,i)) &&
                        pt.counting_in_part((depth,i), containing_part)>=2 &&
                        pt.is_resolution_part(containing_part)
                        {
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
                                pt.add_step_to_part(prem, containing_part);
                                if ps.rule == "resolution" || ps.rule == "th-resoltion"{
                                    pt.set_resolutions_premise(prem); // marks this premise as premise of a resolution if this is a resolution
                                } else if self.preserving_binder.contains(&ps.rule) && pt.is_premise_of_resolution((depth,i)){
                                    pt.set_resolutions_premise(prem); // if its a contraction/reordering, mark the premise only if the step was premise of a resolution
                                }
                            }

                            // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
                            let position = pt.parts[containing_part].part_commands.len();
                            pt.clone_data_to_part((depth,i), containing_part, commands);

                            // Check if this step must be collected in this part
                            if pt.counting_in_part((depth,i), containing_part)>=2 && self.get_clause_len((depth,i), sub_adrs)==1{
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
                            if self.step_is_resolution(prem, sub_adrs){
                                pt.add_step_to_new_part((depth,i), true); // creates new parts for the premises that are resolutions
                            } else {
                                premise_not_r.push(prem); // stores the premises that aren't resolutions
                            }
                        }
                        if !self.single_assume_is_premise((depth,i), commands, sub_adrs){ //check if this step comes from an assume, 
                            //in this case it's premise already is going to be added to part 0.
                            // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
                            // or create a single part for this node and all it's non-resolution premises
                            if premise_not_r.len()>0{ // checks if there is a non-resolution, and if step is not or
                                let non_resolution_parts = pt.non_resolution_parts((depth,i));
                                
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
                            pt.clone_data_to_part((depth,i),containing_part, commands);
                        }
                    }

                    // Case 3
                    // If the node is not a resolution nor premise of one
                    else {
                        for &prem in &ps.premises{
                            // If the premise is a resolution, it will be the conclusion of a new part
                            if self.step_is_resolution(prem, sub_adrs){
                                pt.add_step_to_new_part((depth,i), true); // creates new parts for the premises that are resolutions
                            } 
                            // If the premise is not a resolution, just add it to the parts containing the current step 
                            else {
                                for &containing_part in &containing{
                                    pt.add_step_to_part(prem, containing_part);
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
                    let sp = self.access_subproof(ph_sp);
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
                    
                    let empty: Vec<(usize,usize)> = vec![];
                    let mut premises = &empty;
                    match sp.commands.last(){
                        None => panic!("Why there is an empty subproof on your proof?"),
                        Some(ProofCommand::Step(ps)) => premises = &ps.premises,
                        _ => panic!("Why does your proof has an subproof that doesn't end in a step?"),
                    }

                    // If the subproof is not premise of a resolution, it's resolution premises of same depth will be conclusion of new parts
                    // and it's other premises will be added to it's parts
                    if !pt.is_premise_of_resolution((depth,i)){
                        for &prem in premises{
                            if self.step_is_resolution(prem, sub_adrs) && prem.0==depth{
                                pt.add_step_to_new_part(prem, true);
                            } else {
                                for &containing_parts in &containing {
                                    pt.add_step_to_part(prem, containing_parts);
                                }
                            }
                        }
                    }
                    // If the subproof is premise of a resolution
                    // A logic much like the Case 2 of ProofStep will be used
                    else{
                        let mut premise_not_r: Vec<(usize,usize)> = vec![];
                        for &prem in premises{
                            if self.step_is_resolution(prem, sub_adrs){
                                pt.add_step_to_new_part((depth,i), true); // creates new parts for the premises that are resolutions
                            } else {
                                premise_not_r.push(prem); // stores the premises that aren't resolutions
                            }
                        }
                        
                        // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
                        // or create a single part for this node and all it's non-resolution premises
                        if premise_not_r.len()>0{ // checks if there is a non-resolution, and if step is not or
                            let non_resolution_parts = pt.non_resolution_parts((depth,i));
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
                    // Now the data in the placeholder should be added to the DisjointParts of the Tracker
                    for &containing_part in &containing{    
                        pt.clone_data_to_part((depth,i),containing_part, commands);
                    }
                }
            };
        }
        // Now we will clone the data from outer premises in the respective parts
        for &outer_step in outer_clauses.iter(){
            let mut containing: Vec<usize> = vec![];
            match pt.parts_containing(outer_step.index){
                Ok(v) => containing = v,
                Err(_) => {
                    containing = vec![];
                }
            }
            /*let outer_commands: &Vec<ProofCommand> = match outer_step.index.0{
                0 => &self.proof.commands,
                ind =>  {
                    let owner = self.fetch_owner_subproof(sub_adrs, ind);
                    &self.subproofs[owner].proof.commands
                }
            };*/
            
            let outer_commands: &Vec<ProofCommand> = self.dive_into_proof(outer_step.sp);
            
            //println!("containing: {:?}", &containing);
            for &containing_part in containing.iter(){
                let position = pt.parts[containing_part].part_commands.len();
                //println!("index: {:?}",outer_step);
                //println!("containing part: {:?}", containing_part);
                //println!("outer_commands: {:?}", &outer_commands);
                //println!("outer_commands len: {:?}", outer_commands.len());
                //////////////////////////////////////let current_index = self.map_to_new_loc(outer_step.sp, outer_step.1);
                pt.clone_data_to_part(outer_step.index, containing_part, outer_commands);
                //Check if some outer step must be collected for each part
                if pt.is_premise_of_resolution(outer_step.index) &&
                pt.counting_in_part(outer_step.index, containing_part)>=2 &&
                pt.is_resolution_part(containing_part)
                {
                    pt.add_to_units_queue_of_part(outer_step.index,containing_part, position, &self.subproofs, proof_pool);
                }
                
            }
        }
        pt
    }



    fn fix_broken_proof(&mut self, 
        pt: &mut PartTracker, 
        sub_adrs: Option<usize>, 
        debug_aux: usize, 
        proof_pool: &mut PrimitivePool)
     -> Vec<HashMap<(usize,usize),usize>>{ //ok
        //let sp_stack: &Vec<SubproofMeta> = &self.subproofs;
        let mut ans: Vec<HashMap<(usize, usize), usize>> = vec![];
        for (j,p) in pt.parts.iter_mut().enumerate(){
            let mut to_recompute: Vec<ReResolveInfo> = vec![];
            //let mut subs_table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
            if p.compressible{
                //println!("{:?}",p);
                let mut to_recompute: Vec<ReResolveInfo> = vec![];
                let mut global_to_local: HashMap<(usize,usize),usize> = HashMap::new();
                let n = p.part_commands.len();
                let queue = &p.units_queue;
                let mut changed: HashSet<(usize,usize)> = HashSet::new();
                for &q in queue.iter(){
                    changed.insert(q);
                }
                for (i, step) in p.part_commands.iter().rev().enumerate(){
                    let index = p.original_index[n-1-i];
                    global_to_local.insert(index, n-1-i);
                    if p.all_premises_remain(&self.subproofs, step)
                    && p.some_premises_changed(&self.subproofs, step, &mut changed){
                        to_recompute.push(ReResolveInfo{
                            substitute: false,
                            location: i,
                            index
                        });
                        changed.insert(index);
                    }
                    else if p.single_premise_remains(&self.subproofs, step) &&
                    (step.rule() == "resolution" || step.rule() == "th-resolution") {
                        to_recompute.push(ReResolveInfo{
                            substitute: true,
                            location: i,
                            index
                        });
                        changed.insert(index);
                    }
                    else if p.some_premises_remains(&self.subproofs, step) && 
                    (step.rule() == "resolution" || step.rule() == "th-resolution"){
                        to_recompute.push(ReResolveInfo{
                            substitute: false,
                            location: i,
                            index
                        });
                        changed.insert(index);
                    }
                };

                for clause in to_recompute.iter(){
                    if self.get_rule(clause.index, sub_adrs)=="contraction"{
                        self.re_contract(p, clause.location, sub_adrs, &global_to_local); //WARNING maybe add proof pool
                    }
                    else if clause.substitute{
                        p.substitute(clause.index, p.remaining_premises(&self.subproofs, clause.location)[0]);
                    } else {
                        //println!("clause\nsubstitute: {:?}, location: {:?}, index: {:?}", &clause.substitute, &clause.location, &clause.index);
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
                ans.push(global_to_local);
            }
        }
        ans
    }


    fn reinsert_collected_clauses(&self, pt: &mut PartTracker, sub_adrs: Option<usize>, proof_pool: &mut PrimitivePool){
        let depth = match sub_adrs{
            Some(v) => self.subproofs[v].depth,
            None => 0,
        };
        let void_proof: Vec<ProofCommand> = vec![];
        let mut cache: Vec<&Vec<ProofCommand>> = vec![&void_proof;depth+1];
        cache[depth] = self.dive_into_proof(sub_adrs);
        let mut conclusions: Vec<(usize,PartStep)> = Vec::new();
        for p in pt.parts.iter(){
            let queue = &p.units_queue;
            if p.compressible && queue.len()>0{
                /*if p.depth==0 && depth==0 && p.ind==1{
                    println!("{:?}",p);
                    println!("Queue: {:?}", &p.units_queue);
                }*/
                let queue_local = &p.queue_local;
                let args_queue = &p.args_queue;
                let mut args: Vec<ProofArg> = Vec::new();
                let mut premises: Vec<Premise<'_>> =  Vec::new();
                let command: ProofCommand;
                if let Some(first) = p.part_commands.get(0){
                    let location = p.original_index[0];
                    match &cache[depth][location.1]{
                        ProofCommand::Assume { id, term } => 
                        command = ProofCommand::Assume{id: id.clone(),
                                                       term: first.clause()[0].clone() 
                                                      },
                        ProofCommand::Step(ps) => {
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = first.clause.clone();
                            command = ProofCommand::Step(ps_temp)
                        }
                        ProofCommand::Subproof(ph_sp) => {//Warning: subproof as last step of a part
                            let ad = ph_sp.context_id;
                            let sp = &self.subproofs[ad];
                            let sub_n = sp.commands.len();
                            let mut sub_conclusion = &sp.commands[sub_n-1];
                            if let ProofCommand::Step(ps) = sub_conclusion{
                                let mut ps_temp = ps.clone();
                                ps_temp.clause = first.clause.clone();
                                command = ProofCommand::Step(ps_temp)
                            } else {
                                panic!("The last element of a subproof should be a Step");
                            }
                        }
                    }
                    premises.push(Premise::new((depth, first.ind),&command));
                } else {
                    panic!("What are you doing? Part {:?} is empty.",p.ind);
                }


                let queue_size = queue.len();
                let mut new_commands: Vec<((usize,usize),ProofCommand)> = Vec::new();
                for (i, location) in queue.iter().enumerate(){
                    let local_ind = queue_local[i];
                    let local_step = &p.part_commands[local_ind];
                    let new_comm: ProofCommand;
                    let depth = location.0;
                    if cache[depth].len()==0{
                        let new_sub = match depth{
                            0 => None,
                            i => Some(i-1)
                        };
                        cache[depth] = self.dive_into_proof(new_sub);
                        //cache[depth] = self.dive_into_proof(&sub_adrs[0..depth]);
                    }
                    match &cache[depth][location.1]{
                        ProofCommand::Assume { id, term } => 
                        new_comm = ProofCommand::Assume{id: id.clone(),
                                                       term: local_step.clause[0].clone() 
                                                      },
                        ProofCommand::Step(ps) => {
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = local_step.clause.clone();
                            new_comm = ProofCommand::Step(ps_temp)
                        }
                        ProofCommand::Subproof(sp) => {//Warning: subproof as last step of a part
                                                                  //Should probably be dead code as subproofs introduce new premises
                            let sub_n = sp.commands.len();
                            let sub_conclusion = &sp.commands[sub_n-1];
                            if let ProofCommand::Step(ps) = sub_conclusion{
                                let mut ps_temp = ps.clone();
                                ps_temp.clause = local_step.clause.clone();
                                new_comm = ProofCommand::Step(ps_temp)
                            } else {
                                panic!("The last element of a subproof should be a Step");
                            }
                        }
                    }
                    new_commands.push((*location,new_comm));
                }
                for (l,c) in new_commands.iter(){
                    premises.push(Premise::new(*l,c));
                }
                for (lit, polarity) in args_queue.iter(){
                    args.push(lit.clone());
                    args.push(polarity.clone())
                }
                //println!("{:?}",&p);
                //println!("Queue: {:?}",&queue);
                let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<Vec<_>>(&premises, &args, proof_pool);
                match resolution{
                    Ok(v)=>{
                        let mut conclusion_prem = vec![];
                        for pr in premises.iter(){
                            conclusion_prem.push(pr.index);
                        }
                        let mut new_conclusion = PartStep{
                            ind: p.part_commands.len(),
                            proof_ind: None,
                            premises: conclusion_prem,
                            indirect_premises: vec![],
                            //local_premises: vec![],
                            rule: "resolution".to_string(),
                            clause: v.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect(),
                            args: args,
                            anchor: vec![],
                            context_id: None,
                            sub: false,
                            discharge: vec![],
                        };
                        conclusions.push((p.ind,new_conclusion));
                    }
                        //println!("Result: {:?}\nReinserting on part {:?}.{:?}\nPremises: {:?}\nArguments: {:?}", 
                        //v, n, p.ind, premises, args),
                    
                    Err(_) => panic!("Error: Clauses couldn't be resolved\nReinserting on part {:?}.{:?}\nPremises: {:?}\nArguments: {:?}",
                    depth, p.ind, premises, args),
                }
            }
        }
        for (ind,mut conc) in conclusions.into_iter(){
            let n = pt.parts[ind].part_commands.len();
            //conc.proof_ind = pt.parts[ind].part_commands[n-1].proof_ind;
            pt.parts[ind].part_commands.push(conc);
            pt.parts[ind].compressed = true;
        }
    }

    fn rebuild(&mut self, pt: &mut PartTracker, sub_adrs: Option<usize>){
        let depth = self.stack.len();
        let mut a_count: usize = 0;
        let mut t_count: usize = 0;
        let mut sub_holes: HashMap<usize, OuterPremiseAdrs> = HashMap::new();
        //let mut commands = self.dive_into_proof_mut(sub_adrs);
        let mut table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
        
        let mut premises: IndexSet<Rc<Term>> = IndexSet::new();
        let mut dis_args: Vec<AnchorArg> = Vec::new();
        let mut constant_definitions: Vec<(String,Rc<Term>)> = Vec::new();
        let mut new_commands: Vec<ProofCommand> = vec![];
        
        let assumes = &pt.parts[0].part_commands;
        for a in assumes.iter().rev(){
            let index = a.proof_ind.unwrap();
            if depth==index.0{
                table.insert(index, (depth, new_commands.len()));
                new_commands.push(ProofCommand::Assume { id: format!("a{}", a_count), term: a.clause[0].clone()});
                a_count+=1;
            }
            if depth==0{
                premises.insert(a.clause[0].clone());
            }
            /*else {
                dis_args = build dis_args for subproofs
            }*/
        }
        for part in pt.parts[1..].iter().rev(){
            let mut new_part_conclusion: Option<PartStep> = None;
            let mut m = part.part_commands.len();
            if part.compressed == true{
                //new_part_conclusion = Some(part.part_commands[m-1]);
                m-=1;
            };
            for i in (0..m).rev(){
            //for i in part.part_commands.iter().rev(){
                let s = &part.part_commands[i];
                let index = s.proof_ind.unwrap();
                if !(table.contains_key(&index) || part.removed(&index) || part.marked_for_deletion.contains(&index)) {
                    let n = new_commands.len();
                    //checks if a step in a deeper subproof uses this node as a premise
                    let key = OuterPremiseAdrs{
                        index,
                        sp: sub_adrs
                    };
                    //Saves the location of this step in the new vector
                    if self.new_indexes.contains_key(&key){
                        self.new_indexes.insert(key, Some((depth,n)));
                    }
                    //Fix the address of this step in compressed parts that used it as premise
                    let mut adrs: Vec<(OuterPremiseAdrs,Option<(usize,usize)>)> = vec![];
                    let mut flag_bool = true;
                    {
                        let dependants = self.later_subs_table.get(&key);
                        match dependants{
                            None => flag_bool = false,
                            Some(vec_prem) => {
                                for v in vec_prem{
                                    {   
                                        let c_index: Option<(usize,usize)>;
                                        let cc_index = self.new_indexes.get(v);
                                        match cc_index{
                                            Some(&dd) => c_index = dd,
                                            None => {
                                                let mock = self.dive_into_proof(v.sp);
                                                for mmm in mock{
                                                    println!("{:?}",mmm);
                                                }
                                                println!("key: {:?}\ndeps: {:?}",&key,&dependants);
                                                panic!("SOCORRO! {:?}\n{:?}",&v,&self.new_indexes);

                                            }
                                        }
                                        adrs.push((v.clone(),c_index));
                                        //let mut local_comm = self.dive_into_proof_mut(v.sp);
                                        
                                    }
                                }
                            }
                        }
                    }
                    if flag_bool{
                        let mut flag: Option<usize> = None;
                        for (a,c_index) in adrs{
                            let mut local_comm = self.dive_into_proof_mut(a.sp);
                            let current_index;                                        //
                            match c_index{                                                          //
                                Some(ci) => current_index = ci,                   //
                                None => panic!("There should be a new address here")                //collapse into a function
                            }                                                                       //
                            match &mut local_comm[current_index.1]{
                                ProofCommand::Step(ps) => 
                                for pp in &mut ps.premises{
                                    if *pp==index{
                                        *pp = (depth,n);
                                    }
                                },
                                ProofCommand::Subproof(ph_sp)=>{
                                    let ad = ph_sp.context_id;
                                    flag = Some(ad);
                                }
                                ProofCommand::Assume{..} => panic!("An assume should not be here"),
                                _ => panic!("A step should be here"),
                            }
                        }
                        
                        if let Some(a) = flag{
                            let sp = &mut self.subproofs[a];
                            let sp_len = sp.commands.len();
                            if let ProofCommand::Step(ps) = &mut sp.commands[sp_len-1]{
                                for pp in &mut ps.premises{
                                    if *pp==index{
                                        *pp = (depth,n);
                                    }
                                }
                            }
                        }
                    }
                    self.later_subs_table.remove(&key);
                    table.insert(index, (depth, n));
                    let mut prem: Vec<(usize,usize)> = vec![];
                    for &pr in &s.premises{
                        if pr.0 == depth{
                            match &table.get(&pr){
                                Some(&new_ind) => prem.push(new_ind),
                                None => panic!("Found a clause as premise before adding it to the table")
                            };
                        } else {
                            prem.push(pr);
                            //self.add_to_subs_table(pr, (depth,n), pos_id);
                            //self.later_subs_table.insert(pr,((depth, n))
                        }
                    }
                    if s.sub{//the vertex is a Subproof and it's already compressed
                        let comm = &self.dive_into_proof(sub_adrs)[index.1];
                        
                        if let ProofCommand::Subproof(ssp) = comm{
                            let cid = ssp.context_id;
                            sub_holes.insert(cid, OuterPremiseAdrs{
                                index: (depth, n),
                                sp: sub_adrs,
                            });
                        } else {
                            panic!("Subproof expected");
                        }
                        new_commands.push(comm.clone());
                    }else if &s.rule=="assume"{
                        ();
                    }else{//the vertex is a Step
                        let ps = ProofStep{
                            id: format!("t{}", t_count),
                            clause: s.clause.clone(),
                            rule: s.rule.clone(),
                            premises: prem,
                            args: s.args.clone(),
                            discharge: s.discharge.clone(),
                        };
                        new_commands.push(ProofCommand::Step(ps));
                        t_count+=1;
                    }//Never will be an assume, assumes were all added to part 0, so they are already in the table
                }
            }
        }
        //self.new_indexes.extend(new_indexes);
        self.sub_holes.extend(sub_holes);
        let mut commands = self.dive_into_proof_mut(sub_adrs);
        *commands = new_commands;
    }



    fn process_subproofs(&mut self, sub_adrs: Option<usize>, debug_aux: usize, proof_pool: &mut PrimitivePool) 
    -> (
        HashMap<usize,IndexSet<OuterPremiseAdrs>>, 
        IndexSet<OuterPremiseAdrs>
    ){
        //println!("Processing subproofs on level {debug_aux}");
        let mut all_outer_premises: IndexSet<OuterPremiseAdrs> = IndexSet::new();
        let mut subproofs_to_outer_premises: HashMap<usize,IndexSet<OuterPremiseAdrs>> = HashMap::new();
        let mut subproofs_ind: Vec<usize> = Vec::new();
        let commands: &Vec<ProofCommand>;// = self.dive_into_proof(sub_adrs);
        match sub_adrs{
            Some(j) => commands = &self.subproofs[j].commands,
            None => commands = &self.proof.commands
        };
        for (i, c) in commands.iter().enumerate(){ //collect the index of subproofs
            match c{
                ProofCommand::Subproof(_) => subproofs_ind.push(i),
                _ => ()
            }
        }
        let mut subproof_owned: Vec<Subproof> = vec![];
        let mut q: usize = 0;
        for i in subproofs_ind{
            let m_commands:&mut Vec<ProofCommand>;
            match sub_adrs{
                Some(j) => m_commands = &mut self.subproofs[j].commands,
                None => m_commands = &mut self.proof.commands
            };
            if let ProofCommand::Subproof(sp) = &mut m_commands[i]{
                let ph = Subproof::new_placeholder(self.stack.len()+q);
                q+=1;
                subproof_owned.push(mem::replace(sp,ph));
            }else{
                panic!("There is an error in the logic. This index is computed as the index of a subproof, yet there is no subproof in this index")
            }
        }
        for s in subproof_owned.into_iter(){
            self.give_subproof_to_compressor(s);
            let current_adrs = self.sp_count;
            self.stack.push(current_adrs.unwrap());
            let sp_result = self.lower_units(current_adrs, debug_aux, proof_pool);
            self.stack.pop();
            match sp_result{
                Ok(sp_premises) => {
                    all_outer_premises.extend(sp_premises.iter().cloned());
                    subproofs_to_outer_premises.insert(current_adrs.unwrap(), sp_premises);
                },
                Err(_) => panic!("Some subproof coudn't be compressed")
            }
        }
        (subproofs_to_outer_premises, all_outer_premises)
    }*/

    fn get_rule(&self, step: (usize, usize), sub_adrs: Option<usize>) -> &str{ //ok
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => "assume",
            Some(ProofCommand::Step(ps)) => &ps.rule,
            Some(ProofCommand::Subproof(ssp)) => {
                let sp = self.access_subproof(ssp);
                sp.commands.last().unwrap().rule()
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
                let sp = self.access_subproof(ssp);
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => sub_ps.clause.len(),
                    Some(_) => panic!("The last step of a subproof should be a step"),
                    None => panic!("This subproof shouldn't be empty")
                }
            }
            None => panic!("Index out of bound for the command vector")
        }
    }

    /*fn get_premises(&self, step: (usize,usize), sub_adrs: Option<usize>) -> Option<&Vec<(usize, usize)>>{
        let ind = step.1;
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        /*for i in commands.iter(){
            println!("{:?}",i);
        }*/
        match commands.get(ind){
            Some(ProofCommand::Assume {..}) => None,
            Some(ProofCommand::Step(ps)) => Some(&ps.premises),
            Some(ProofCommand::Subproof(ssp)) => {
                let sp = &self.subproofs[ssp.context_id];
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => Some(&sub_ps.premises),
                    Some(_) => panic!("The last step of a subproof should be a step"),
                    None => panic!("This subproof shouldn't be empty")
                }
            }
            None => panic!("Index out of bound for the command vector")
        }
    }*/

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
            let owner = self.fetch_owner_subproof(sub_adrs, step.0);
            commands = &self.subproofs[owner].proof.commands;
        }
        match commands.get(ind){
            Some(ProofCommand::Step(ps)) => ps.rule=="resolution" || ps.rule =="th-resolution",
            Some(_) => false,
            None => panic!("This command doesn't exist")
        }
    }
    

    fn resolution_is_a_premise(&self, step: &ProofStep, sub_adrs: Option<usize>) -> bool{ //ok
        if step.premises.len()!=1{
            panic!("Contraction/reordering from not exactly 1 premise");
        } else {
            let coming_from = step.premises[0];
            let (depth, ind) = coming_from;
            
            let commands: &Vec<ProofCommand>;
            if depth == 0{
                commands = &self.proof.commands;
            } else {
                let owner = self.fetch_owner_subproof(sub_adrs, depth);
                commands = &self.subproofs[owner].proof.commands;
            }
            match commands.get(ind){
                Some(ProofCommand::Step(ps)) => {
                    ps.rule == "resolution" || ps.rule == "th-resolution"
                }
                Some(_) => false,
                None => panic!("This command doesn't exist")
            }
        }
    }


    
    fn dive_into_proof(&self, sub_adrs: Option<usize>) -> &Vec<ProofCommand>{ //ok
        match sub_adrs{
            None => &self.proof.commands,
            Some(i) => &self.subproofs[i].proof.commands
        }
    }
    /*

    fn subproof_id(sp: &Subproof) -> String{
        match sp.commands.last().unwrap(){
            ProofCommand::Step(ps) => ps.id.clone(),
            _ => panic!("The end of a subproof should always be a step")
        }
    }

    */
    fn dive_into_proof_mut(&mut self, sub_adrs: Option<usize>) -> &mut Vec<ProofCommand>{ //ok
        match sub_adrs{
            None => &mut self.proof.commands,
            Some(i) => &mut self.subproofs[i].proof.commands
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
                    let parent_clause: Vec<Rc<Term>> = part.part_commands[*parent_local_ind].clause().clone().to_vec();
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
                } else if new_clause.len()==0 {
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
    (Vec<Rc<Term>>,Vec<(usize,usize)>,Vec<ProofArg>){
        let sp_stack: &Vec<SubproofMeta> = &self.subproofs;
        let step = &mut part.part_commands[index];
        let mut remaining: Vec<(usize, usize)> = part.remaining_premises(sp_stack, index);
        let table: &HashMap<(usize, usize), (usize, usize)> = &part.subs_table;
        let mut new_commands: Vec<(ProofCommand,(usize,usize))> = Vec::new();
        let mut premises: Vec<Premise<'_>> = self.build_premises(part, &remaining, global_to_local, index, sub_adrs, &mut new_commands);
        let args = self.build_args(part, &remaining, index);
        // substituting premises
        for r in remaining.iter_mut(){
            match table.get(r){
                Some(rr) => {
                    for p in premises.iter_mut() {
                        if p.index==*r{
                            p.index = *rr;
                            let local_ind: usize = *global_to_local.get(rr).unwrap();
                            p.clause = &part.part_commands[local_ind].clause();
                        }
                    }
                    *r = *rr;
                }
                None => ()
            }
        }
        if part.is_behaved(index){      // This step will be contracted or reordered in future, 
                                                    // so here the result will be a vector to avoid contracting it now
            let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<Vec<_>>(&premises, &args, proof_pool);
            match resolution{
                Ok(r) => {
                    let resolvent: Vec<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                    let formatted_premises = premises.iter().map(|x| x.index).collect();
                    (resolvent, formatted_premises, args)
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
        remaining: &Vec<(usize, usize)>, 
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
        let remaining_set: HashSet<_> = remaining.iter().cloned().collect();
        
        let op_prem: Option<&Vec<(usize, usize)>> = data.premises(sp_stack);
        if let Some(prem) = op_prem{
            for p in prem.iter(){
                if remaining_set.contains(p){
                    let new_comm: ProofCommand;
                    if cache[p.0].len()==0{
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
                        ProofCommand::Assume { id, term } => 
                        new_comm = ProofCommand::Assume{id: id.clone(),
                                                        term: local_step.clause()[0].clone() 
                                                        },
                        ProofCommand::Step(ps) => {
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = local_step.clause().clone().to_vec();
                            new_comm = ProofCommand::Step(ps_temp)
                        }
                        ProofCommand::Subproof(ph_sp) => {
                            let sp = self.access_subproof(ph_sp);
                            let sub_conclusion = sp.commands.last().unwrap();
                            if let ProofCommand::Step(ps) = sub_conclusion{
                                let mut ps_temp = ps.clone();
                                ps_temp.clause = local_step.clause().clone().to_vec();
                                new_comm = ProofCommand::Step(ps_temp)
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
            ans.push(Premise::new(*loc,&c));
        }
        ans
    }    

    fn build_args(&self, part: &DisjointPart, remaining: &Vec<(usize, usize)>, index: usize) -> Vec<ProofArg>{ // ok
        let mut ans: Vec<ProofArg> = vec![];
        let sp_stack = &self.subproofs;
        let data = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().cloned().collect();
        let old_args = data.args(); 
        if let Some(premises) = data.premises(sp_stack){
            if remaining_set.contains(&premises[0]){
                ans.push(old_args[0].clone());
                ans.push(old_args[1].clone());
            }
            for (i, &p) in premises.iter().skip(2).enumerate(){
                if remaining_set.contains(&p){
                    let j = i+2;
                    ans.push(old_args[2*j-2].clone());
                    ans.push(old_args[2*j-1].clone());
                }
            }
        }
        ans
    }

    /*fn add_to_subs_table(&mut self, prem: (usize,usize), dependant: (usize, usize), sp_id: Vec<usize>){
        self.later_subs_table.entry(prem).or_insert(Vec::new()).push((dependant,sp_id));
    }

    fn get_commands_from_positional_adrs(&self, pos_adrs: &[usize]) -> usize{
        match &self.positional_adrs_to_sp.get(pos_adrs){
            Some(i) => **i,
            None => panic!("Could not recover subproof ref index")
        }
    }*/
/*
    fn give_subproof_to_compressor(&mut self, s: Subproof){
        self.subproofs.push(s);
        self.sp_count = match self.sp_count{
            None => Some(0),
            Some(i) => Some(i+1)
        };
    }

    fn mark_outer_premise(&self, outer_premises: &mut IndexSet<OuterPremiseAdrs>, later_subs_table: &mut HashMap<OuterPremiseAdrs,Vec<OuterPremiseAdrs>>, prem: (usize,usize), step:(usize,usize), sub_adrs: Option<usize>){
        let dependency: OuterPremiseAdrs;
        if prem.0 !=0 {
            dependency = OuterPremiseAdrs{
                            index: prem,
                            sp: Some(self.stack[prem.0-1]),
                        };
        } else {
            dependency = OuterPremiseAdrs{
                            index: prem,
                            sp: None,
                        };
        };
        outer_premises.insert(dependency.clone());
        let key = OuterPremiseAdrs{
            index: step,
            sp: sub_adrs
        };
        later_subs_table.entry(key).or_insert(Vec::new()).push(dependency);
    }
*/
    pub fn access_subproof(&self, placeholder: &Subproof) -> &Subproof{ //ok
        &self.subproofs[placeholder.context_id].proof
    }

    pub fn access_subproof_mut(&mut self, placeholder: &Subproof) -> &mut Subproof{ //ok
        &mut self.subproofs[placeholder.context_id].proof
    }

    fn must_be_a_new_conclusion(&self, step: (usize, usize), pt: &PartTracker, sub_adrs: Option<usize>)->bool{ //ok
        let fixed;
        match sub_adrs{
            Some(v) => fixed = &self.subproofs[v].fixed,
            None => fixed = &self.fixed_clauses
        }
        !pt.is_conclusion.contains(&step) && fixed.contains(&step)
    }

    fn single_assume_is_premise(&self, step: (usize, usize), commands: &Vec<ProofCommand> ,sub_adrs: Option<usize>) -> bool{
        match &commands[step.1]{
            ProofCommand::Step(ps) => {
                if ps.premises.len()!=1{
                    false
                } else {
                    let prem = ps.premises[0];
                    if prem.0==step.0{
                        commands[prem.1].is_assume()
                    } else if prem.0==0{
                        self.proof.commands[prem.1].is_assume()
                    } else {
                        let ind = self.fetch_owner_subproof(sub_adrs, prem.0);
                        self.subproofs[ind].proof.commands[prem.1].is_assume()
                    }
                }
            }
            _ => false,
        }
    }

    /*pub fn clause_len(&self, sp_stack: &Vec<Subproof>) -> usize{
        match &self{
            ProofCommand::Assume{..} => 1,
            ProofCommand::Step(ps) => ps.clause.len(),
            ProofCommand::Subproof(ssp) => {
                let sp = &sp_stack[ssp.context_id];
                match sp.commands.last(){
                    Some(pc) => {
                        match pc{
                            ProofCommand::Step(ps) => ps.clause.len(),
                            _ => panic!("The last command of a subproof should be a step")
                        }
                    }
                    None => panic!("An empty subproof doesn't concludes anything. This proof is wrong")
                }
            }
        }
    }*/

    fn print_part(&self, part: &DisjointPart){
        println!("Part {:?}", part.ind);
        for (i, com) in part.part_commands.iter().enumerate(){
            match com{
                ProofCommand::Assume { id, term } => println!("{:?} - Assume {:?}: {:?}",i,id,term),
                ProofCommand::Step(ps) => 
                println!("{:?} - Step {:?} {:?}: {:?}; prem: {:?}; arg: {:?}",i,&ps.id,&ps.rule,&ps.clause,&ps.premises, &ps.args),
                ProofCommand::Subproof(sp_ph) => {
                    let sp = self.access_subproof(sp_ph);
                    match sp.commands.last(){
                        None => panic!("empty"),
                        Some(ProofCommand::Step(ps)) => println!("{:?} - Sub {:?} {:?}: {:?}; prem: {:?}; disc: {:?}",i,&ps.id,&ps.rule,&ps.clause,&ps.premises, &ps.discharge),
                        _ => panic!("Not a proofstep")
                    };
                }
            }
        }
    }
    //fn map_to_new_loc(&self, outer_step: OuterPremiseAdrs) -> usize{}
}

