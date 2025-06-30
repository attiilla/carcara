//Question: outer_premises that aren't resolution can be thrown out after cloning their data to the parts?
//benchmarks/small/SH_problems_all_filtered/Green_veriT/x2020_07_28_19_01_13_405_7253502.smt2 rodando ~/carcara/wt-atila/target/release/carcara check -i --allow-int-real-subtyping --expand-let-bindings test.alethe x2020_07_28_19_01_13_405_7253502.smt2
//build_term!(pool, (not { term }))
//To optimize: steps without premises can all go to part 0?
//To optimize: references in parts
//To optimize: mark as resolution premise only if not resolution
//CORNER CASE TO TEST: When part conclusion is substituted
//CORNER CASE TO TEST: Node is a subproof that isn't used as premise for any node of same depth
//CORNER CASE TO TEST: is_premise_of_part_conclusion must check if the conclusion is a pseudo-resolution
mod tracker;
mod disjoints;
mod error;
use crate::{
    ast::{
        proof::*,
        pool::PrimitivePool,
        rc::Rc,
        term::Term,
    },
    checker::{
        error::CheckerError,
        rules::Premise,
        rules::resolution::{apply_generic_resolution, binary_resolution, unremove_all_negations},
    },
    compressor::error::*,
};

use std::{
    collections::{HashSet, HashMap},
    fmt,
    env,
    mem,
    time::{Duration, Instant}, 
    vec,
};

use disjoints::*;
use indexmap::IndexSet;
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

    // Maps the outer steps used by the proof to their original proof sub_adrs
    // Always empty here, added just for consistency
    outer: HashMap<usize,(Vec<usize>, Option<usize>)>,

}

#[derive(Clone, Debug)]
pub struct CompressorStatistics{
    pub file_name: String,
    pub collect_units: Duration,
    pub fix_broken_proof: Duration,
    pub reinsert: Duration,
    pub rebuild: Duration,
    pub reassemble: Duration,
    pub total: Duration,
    pub original_size: usize,
    pub final_size: Option<usize>,
}

impl fmt::Display for CompressorStatistics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn format_duration(d: Duration) -> String {
            let num = d.as_secs_f64() * 1000.0;
            num.to_string().replace('.', ",")
        }
        let compression: String = match self.final_size{
            Some(s) => {
                let c = (s as i64)-(self.original_size as i64);
                c.to_string()
            }
            None => "None".to_owned()
        };
        write!(
            f,
            "{};{:?};{:?};{:?};{:?};{:?};{:?};{};{};{}",
            self.file_name,
            format_duration(self.collect_units),
            format_duration(self.fix_broken_proof),
            format_duration(self.reinsert),
            format_duration(self.rebuild),
            format_duration(self.reassemble),
            format_duration(self.total),
            self.original_size,
            self.final_size.map_or("".to_owned(), |s| format!("{}", s)),
            compression
        )
    }
}

#[derive(Debug)]
struct SubproofMeta{
    proof: Subproof,
    fixed: HashMap<(usize,usize),Option<(usize,usize)>>, // same as in ProofCompressor
    depth: usize,
    outer: HashMap<usize,(Vec<usize>, Option<usize>)>, // almost the same as in ProofCompressor, but not always empty here
    new_ind: usize,
    parent_adrs: Option<usize>,
    discharge: Vec<(usize,usize)>,

}

#[derive(Debug)]
struct ReResolveInfo{
    substitute: bool,
    location: usize,
    index: (usize, usize),
    rule: String,
}

#[derive(Debug)]
struct ReResolveReturn{
    clause: Vec<Rc<Term>>,
    premises: Vec<(usize,usize)>,
    args: Vec<Rc<Term>>,
}

type ResolveResult<'a> = Result<(IndexSet<(u32, &'a Rc<Term>)>,Vec<usize>), CheckerError>;


impl<'a,'b> ProofCompressor{
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

    pub fn compress_proof(mut self, verbose: bool, proof_pool: &mut PrimitivePool, mut stats: Option<&mut CompressorStatistics>) -> Proof{
        let now = Instant::now();
        env::set_var("RUST_BACKTRACE", "1");
        if verbose{
            let _ = self.lower_units_verbose(None, proof_pool, None);
            let _ = self.reassemble(None);
        } else {
            
            let s = self.lower_units(None,  proof_pool, stats);
            // remove the placeholders and insert the subproofs again in the final proof
            let reassembly_start = Instant::now();
            let s = self.reassemble(s);
            let reassemble_time = reassembly_start.elapsed();
            if let Some(stats) = s{
                stats.reassemble = reassemble_time;
                stats.total = now.elapsed();
                eprintln!("{}",stats);
            }
        };
        self.proof
    }

    fn lower_units(
        &'a mut self, 
        sub_adrs: Option<usize>, 
        proof_pool: &mut PrimitivePool, 
        stats: Option<&'b mut CompressorStatistics>
    ) -> Option<&'b mut CompressorStatistics> 
    {
        // Check for steps that can't be deleted and subproof locations
        // Collect every subproof into an array and replace them with placeholders
        if sub_adrs.is_none(){
            self.relocate_subproofs(sub_adrs);
        }
        match stats{
            Some(s)=>{
                // Counts the size of the proof
                if sub_adrs.is_none(){
                    s.original_size = self.proof.commands.len();
                    for sub in &self.subproofs{
                        s.original_size += sub.proof.commands.len();
                    }
                }

                // Break the proof in parts that have only resolution and preserving binders
                // Then, collect units that are used more than once before the last step
                let (d_collect, mut pt) = self.collect_units(sub_adrs, proof_pool);
                s.collect_units+=d_collect;
                
                // Turn every part of a proof in a valid reasoning
                let d_fix = self.fix_broken_proof(&mut pt, sub_adrs, proof_pool);
                s.fix_broken_proof+=d_fix;
                
                // Reinsert the collected units to each part
                let d_rein = self.reinsert_collected_clauses(&mut pt, sub_adrs, proof_pool);
                s.reinsert+=d_rein;
                
                // Combines the parts to create a valid proof
                let (d_reb,new_commands) = self.rebuild(&mut pt, sub_adrs);
                s.rebuild+=d_reb;

                self.position_insert(new_commands, sub_adrs);

                // Calls this same algorithm over every subproof
                if sub_adrs.is_none(){
                    for i in 0..self.subproofs.len(){
                        self.lower_units(Some(i), proof_pool, Some(s));
                    }
                }
                Some(s)
            }
            None => {
                // Break the proof in parts that have only resolution and preserving binders
                // Then, collect units that are used more than once before the last step
                let (_, mut pt) = self.collect_units(sub_adrs, proof_pool);
                
                // Turn every part of a proof in a valid reasoning
                self.fix_broken_proof(&mut pt, sub_adrs, proof_pool);
                
                // Reinsert the collected units to each part
                self.reinsert_collected_clauses(&mut pt, sub_adrs, proof_pool);
                
                // Combines the parts to create a valid proof
                let (_, new_commands) = self.rebuild(&mut pt, sub_adrs);
                self.position_insert(new_commands, sub_adrs);

                // Calls this same algorithm over every subproof
                if sub_adrs.is_none(){
                    for i in 0..self.subproofs.len(){
                        self.lower_units(Some(i), proof_pool, None);
                    }
                }
                None
            }
        }
    }

    fn lower_units_verbose(
        &'a mut self, 
        sub_adrs: Option<usize>, 
        proof_pool: &mut PrimitivePool, 
        _stats: Option<&'b mut CompressorStatistics>
    ) -> Option<&'b mut CompressorStatistics> 
    {
        // Check for steps that can't be deleted and subproof locations
        // Collect every subproof into an array and replace them with placeholders
        println!("verbiage {:?}", sub_adrs);
        if sub_adrs.is_none() | (sub_adrs==Some(3)){
            print_proof(self.dive_into_proof(sub_adrs), "".to_owned(), 0, 0);

        }
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
        let (mut _d, mut pt) = self.collect_units(sub_adrs, proof_pool);
        for p in &pt.parts{
                self.print_part(p);
                println!("Collected: {:?}", &p.units_queue);
        }
    
        // turn every part of a proof in a valid reasoning
        self.fix_broken_proof(&mut pt, sub_adrs, proof_pool);
        println!("after fix");
        for p in &pt.parts{
                self.print_part(p);
                println!("Substituted: {:?}",&p.subs_table);
        }
        

        // reinsert the collected units to each part
        self.reinsert_collected_clauses(&mut pt, sub_adrs, proof_pool);
        println!("after reinsert");
        for p in &pt.parts{
            self.print_part(p);
        }


        // combines the parts to create a valid proof
        let new_commands: Vec<ProofCommand> = self.rebuild_verbose(&mut pt, sub_adrs);
        self.position_insert(new_commands, sub_adrs);
        

        //calls this same algorithm over every subproof
        if sub_adrs.is_none(){
            for i in 0..self.subproofs.len(){
                self.lower_units_verbose(Some(i), proof_pool, None);
            }
        }
        None
    }

    // This functions receives the current address of a subproof level and a target level, then
    // it looks for the subproof of target level that contains the current proof and return
    // the address of this proof level
    fn stalk_owner(&self, sub_adrs: Option<usize>, tgt: usize) -> Option<usize>{ //ok //Change
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

    // Returns the address of the last subproof inside the subproof addressed by sub_adrs
    fn recursively_implicit_premises(&self, adrs: usize, src_depth: usize) -> IndexSet<(usize,usize)>{

        let mut ans: IndexSet<(usize,usize)> = 
        match self.subproofs[adrs].outer.get(&(src_depth)){
            Some((v,_)) => v.iter().map(|&x| (src_depth, x)).collect(),
            None => IndexSet::new(),
        };
        if let Some(next_sub) = self.subproofs.get(adrs+1){
            if next_sub.depth > src_depth+1{
                ans.append(&mut self.recursively_implicit_premises(adrs+1, src_depth));
            }   
        }
        ans
    }

    fn relocate_subproofs(&mut self, sub_adrs: Option<usize>){ //ok
        let depth: usize = self.get_depth(sub_adrs);

        let mut subproof_indexes: Vec<usize> = vec![];
        let mut fixed_clauses: Vec<(usize,usize)> = vec![];
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        for (i, c) in commands.iter().enumerate(){ //finds subproofs and outer premises
            for &prem in c.premises(){
                if prem.0!=depth{
                    fixed_clauses.push(prem); //lists outer premises
                }
            }
            if matches!(c,ProofCommand::Subproof(_)){
                subproof_indexes.push(i);
            }
        }
        
        for &prem in &fixed_clauses{ //set the clauses as fixed
            self.tidy_up_outer_dependencies(prem,sub_adrs);
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

    fn handle_internal_command(&self, 
        pt: &mut PartTracker, 
        command: &ProofCommand, 
        outer_premises: &mut IndexSet<(usize,usize)>, 
        ind: (usize, usize), 
        sub_adrs: Option<usize>, 
        proof_pool: &mut PrimitivePool)
    {
        if let ProofCommand::Step(ps) = command{
            let depth: usize = ind.0;
            let mut containing: Vec<usize> = pt.get_containing_parts(ind, true);
            if self.must_be_a_new_conclusion(ind, pt, sub_adrs){
                let new_part_ind: usize = pt.add_step_to_new_part(ind, true);
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
                    pt.mark_for_part(prem, containing_part);
                    pt.set_as_resolution_premise(prem);
                }
                
                let position = pt.parts[containing_part].part_commands.len();
                pt.insert_to_part(ind, containing_part, command);

                if pt.must_be_collected(ind, containing_part, command){
                    pt.add_to_units_queue_of_part(ind,containing_part, position, command, proof_pool);
                }
            }
        } else {
            panic!("This function must never be called for a non-step command");
        }
    }

    fn handle_edge_command(&self, 
        pt: &mut PartTracker, 
        c: &ProofCommand, 
        commands: &[ProofCommand],
        ind: (usize, usize),
        sub_adrs: Option<usize>,
        proof_pool: &mut PrimitivePool
    ){
        let depth: usize = ind.0;
        let is_subproof: bool = matches!(c, ProofCommand::Subproof(_));
        let containing: Vec<usize> = pt.get_containing_parts(ind, true);
        let mut premise_not_r: Vec<(usize,usize)> = vec![];
        if is_subproof{
            for &prem in &self.implicit_premises(c, depth){
                if prem.0==depth{
                    if self.step_is_resolution(prem, sub_adrs){
                        pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions
                    } else {
                        premise_not_r.push(prem); // stores the premises that aren't resolutions
                    }
                }
            }
        } else {
            for &prem in c.premises(){
                if prem.0==depth{
                    if self.step_is_resolution(prem, sub_adrs){
                        pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions
                    } else {
                        premise_not_r.push(prem); // stores the premises that aren't resolutions
                    }
                }
            }
        }

        //check if this step comes from an assume and nothing more, 
        // In this case it's premise already is going to be added to part 0.
        if !self.is_pseudo_assume(ind, commands, sub_adrs){ 
            // Here we will add the non-resolution premises to non-resolution parts where this node belongs to 
            // or create a single part for this node and all it's non-resolution premises
            if !premise_not_r.is_empty(){ // checks if there is a non-resolution, and if step is not or
                let new_part_ind: usize = pt.add_step_to_new_part(ind, false);
                for &prem in &premise_not_r{
                    pt.mark_for_part(prem, new_part_ind);
                }
            }
        }
        
        // Now the data in the ProofCommand is added to the DisjointParts of the Tracker
        for &containing_part in &containing{
            let position = pt.parts[containing_part].part_commands.len();
            pt.insert_to_part(ind,containing_part, c);

            if pt.parts[containing_part].compressible && !is_subproof{
                // Check if this step must be collected in this part
                if pt.must_be_collected(ind, containing_part, c){
                    pt.add_to_units_queue_of_part(ind,containing_part, position, c, proof_pool);
                }
            }
        }
    }

    fn handle_uncompressible_command(&self, 
        pt: &mut PartTracker, 
        c: &ProofCommand,
        ind: (usize, usize),
        sub_adrs: Option<usize>
    ){
        let depth: usize = ind.0;
        let is_subproof = matches!(c, ProofCommand::Subproof(_));
        let containing: Vec<usize> = pt.get_containing_parts(ind, self.is_resolution_or_pseudo(c,sub_adrs));
        if is_subproof{
            for &prem in &self.implicit_premises(c, depth){
                if prem.0==depth{
                    // If the premise is a resolution, it will be the conclusion of a new part
                    if self.step_is_resolution(prem, sub_adrs){
                        pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions
                    } 
                    // If the premise is not a resolution, just add it to the parts containing the current step 
                    else {
                        for &containing_part in &containing{
                            pt.mark_for_part(prem, containing_part);
                        }
                    }
                }
            }
        } else {
            for &prem in c.premises(){
                if prem.0==depth{
                    // If the premise is a resolution, it will be the conclusion of a new part
                    if self.step_is_resolution(prem, sub_adrs){
                        pt.add_step_to_new_part(prem, true); // creates new parts for the premises that are resolutions
                    } 
                    // If the premise is not a resolution, just add it to the parts containing the current step 
                    else {
                        for &containing_part in &containing{
                            pt.mark_for_part(prem, containing_part);
                        }
                    }
                }
            }
        };
        for &containing_part in &containing{
            // Now the data in the ProofStep should be added to the DisjointParts of the Tracker
            pt.insert_to_part(ind,containing_part, c);
        }
    }

    fn handle_collectible_outer_premises(&self, 
        collectible_outer_premises: &mut IndexSet<(usize, usize)>, 
        pt: &mut PartTracker, 
        sub_adrs: Option<usize>,
        proof_pool: &mut PrimitivePool)
    {
        let outer_owners: &HashMap<usize, (Vec<usize>, Option<usize>)> = match sub_adrs{
            Some(v) => {
                &self.subproofs[v].outer
            }
            None => &self.outer
        };
        for &outer_step in collectible_outer_premises.iter(){
            let outer_owner_address: Option<usize> = outer_owners.get(&outer_step.0).unwrap_or_else(|| 
                panic!("Outer step {:?} not mapped on compressor of {:?}", &outer_step, sub_adrs)
            ).1;
            let adjusted_outer_step: (usize, usize) = self.get_new_index_of_outer_premise(sub_adrs, outer_step);
            let outer_commands: &Vec<ProofCommand> = self.dive_into_proof(outer_owner_address);
            let outer_c = &outer_commands[adjusted_outer_step.1];
            let containing: Vec<usize> = match pt.parts_containing(outer_step){
                Ok(v) => v,
                _ => panic!("This should be impossible. In the same loop this step was stored in 
                collectible_outer_premises it should have been marked for some part")
            };

            for &containing_part in &containing{
                let position = pt.parts[containing_part].part_commands.len();
                pt.insert_to_part(adjusted_outer_step, containing_part, outer_c);

                
                if pt.must_be_collected(outer_step, containing_part, outer_c)
                {
                    pt.add_to_units_queue_of_part(outer_step, containing_part, position, outer_c, proof_pool);
                }
                
            }
        }
    }

    fn collect_units(&mut self, sub_adrs: Option<usize>, proof_pool: &mut PrimitivePool) -> (Duration, PartTracker){
        let now = Instant::now();
        let mut collectible_outer_premises: IndexSet<(usize,usize)> = IndexSet::new();
        let depth: usize = self.get_depth(sub_adrs);
        let commands: &Vec<ProofCommand> = self.dive_into_proof(sub_adrs);
        let n = commands.len();
        let mut pt = PartTracker::new(self.step_is_resolution((depth,n-1), sub_adrs));
        pt.mark_for_part((depth,n-1),1); //adds conclusion to part 1
        pt.set_is_conclusion((depth,n-1));
        for (i, c) in commands.iter().enumerate().rev(){
            match c{
                ProofCommand::Assume{..} => {
                    pt.mark_for_part((depth,i), 0); //all assumes must be in the part 0
                    let containing: Vec<usize> = match pt.parts_containing((depth,i)){
                        Ok(v) => v,
                        Err(CollectionError::NodeWithoutInwardEdge) => 
                            panic!("This error should be impossible in this part of the code.\nThis node was added to part 0 just some lines above"),
                        Err(_) => panic!("Unexpected error"),
                    };

                    for &containing_part in &containing{
                        let position = pt.parts[containing_part].part_commands.len();
                        pt.insert_to_part((depth,i),containing_part, c);
                        if pt.must_collect_assume((depth,i), containing_part)
                        {
                            pt.add_to_units_queue_of_part((depth,i),containing_part, position, c, proof_pool);
                        }
                    }
                    
                }

                ProofCommand::Step(ps) => {
                    // Case 1
                    // If this node is a resolution, every premise is in the same parts
                    if self.internal_command(ps,sub_adrs){
                        self.handle_internal_command(&mut pt, c, &mut collectible_outer_premises, (depth,i), sub_adrs, proof_pool);
                    }

                    // Case 2
                    // If this node is not a resolution but is premise of a resolution,
                    // it will be in the same parts as the resolutions who use it, but the
                    // disjoint part can't grown from here
                    else if pt.is_premise_of_resolution((depth,i)){
                        self.handle_edge_command(&mut pt, c, commands, (depth,i), sub_adrs, proof_pool);
                    }

                    // Case 3
                    // If the node is not a resolution nor premise of one
                    else {
                        self.handle_uncompressible_command(&mut pt, c, (depth, i), sub_adrs);
                    }
                }
                
                ProofCommand::Subproof(_) => {
                    //WARNING Corner Case: Let with premise in another depth
                    //CORNER CASE TO TEST: in get_containing_parts: Node is a subproof that isn't used as premise for any node of same depth

                    // Case 1
                    // If this node is premise of a resolution, it will be 
                    // in the same parts as the resolutions who use it, but the
                    // disjoint part can't grown from here
                    if pt.is_premise_of_resolution((depth,i)){
                        self.handle_edge_command(&mut pt, c, commands, (depth,i), sub_adrs, proof_pool);
                    }
                    // Case 2
                    // If the node is not a resolution nor premise of one
                    else{
                        self.handle_uncompressible_command(&mut pt, c, (depth, i), sub_adrs);
                    }
                    
                }
            };
        }
        self.handle_collectible_outer_premises(&mut collectible_outer_premises, &mut pt, sub_adrs, proof_pool);
        let elapsed = now.elapsed();
        (elapsed, pt)
    }

    fn fix_broken_proof(&mut self, 
        pt: &mut PartTracker, 
        sub_adrs: Option<usize>, 
        proof_pool: &mut PrimitivePool) -> Duration
    {
        let now = Instant::now();
        let depth: usize = self.get_depth(sub_adrs);        
        for p in &mut pt.parts{
            if p.compressible{
                let mut to_recompute: Vec<ReResolveInfo> = vec![];
                let n: usize = p.part_commands.len();
                let queue: &IndexSet<(usize, usize)> = &p.units_queue;
                let mut modified: HashSet<(usize,usize)> = HashSet::new();
                for &q in queue{
                    modified.insert(q);
                }
                for (local_ind, c) in p.part_commands.iter().enumerate().rev(){
                    let index: (usize, usize) = p.original_index[local_ind];
                    if p.must_be_recomputed(c, &mut modified) & (depth==index.0){
                        to_recompute.push(
                        ReResolveInfo{
                            substitute: false,
                            location: local_ind,
                            index,
                            rule: c.rule().to_owned()
                        });
                        modified.insert(index);
                    }
                    else if p.must_be_substituted(c) & (depth==index.0){
                        to_recompute.push(
                        ReResolveInfo{
                            substitute: true,
                            location: local_ind,
                            index,
                            rule: c.rule().to_owned()
                        });
                        modified.insert(index);
                    }
                };
                for clause in &to_recompute{
                    if clause.rule=="contraction"{
                        self.re_contract(p, clause.location, sub_adrs);
                    }
                    else if clause.substitute{
                        p.substitute(clause.index, p.remaining_premises(clause.location)[0]);
                    } else {
                        let recomputed: ReResolveReturn = self.re_resolve(
                                p, 
                                clause.location, 
                                sub_adrs, 
                                proof_pool
                            );
                        let new_clause: Vec<Rc<Term>> = recomputed.clause;
                        let new_premises: Vec<(usize, usize)> = recomputed.premises;
                        let _new_args: Vec<Rc<Term>> = recomputed.args;
                        p.set_recomputed(clause.index);
                        match &mut p.part_commands[clause.location]{
                            ProofCommand::Assume { .. } => panic!("Assumes don't have args nor premises"),
                            ProofCommand::Step(ps) => {
                                ps.args = vec![];
                                ps.premises = new_premises;
                                ps.clause = new_clause;
                            },
                            ProofCommand::Subproof(_) => panic!("You shouldn't change this from outside of the subproof"),
                        }
                    }
                }
            }
        }
        let elapsed = now.elapsed();
        elapsed
    }

    fn reinsert_collected_clauses(
        &self, 
        pt: &mut PartTracker, 
        sub_adrs: Option<usize>, 
        proof_pool: &mut PrimitivePool) -> Duration
    {
        let now = Instant::now();
        let depth = self.get_depth(sub_adrs);
        let mut cache = ProofCache::new(self, sub_adrs);

        // Stores the conclusion on each part and the part index
        let mut conclusions: Vec<(usize,ProofCommand)> = Vec::new();
        for p in & pt.parts{
            let queue = &p.units_queue;
            if p.compressible && !queue.is_empty(){
                let mut args;
                let queue_local = &p.queue_local;
                let args_queue = &p.args_queue;
                let mut premises: Vec<Premise<'_>>=  Vec::new();

                // The part was constructed traversing the proof bottom-up
                // So the 0-th position contains the conclusion
                let mut _first: &ProofCommand = &p.part_commands[0];
                let mut location: (usize, usize) = p.original_index[0];
                // Verifies if the conclusion was substituted
                (_first, location) = p.resolve_substitute(_first, location);


                if let ProofCommand::Step(ps) = cache.get(location){
                    // Here will be added the premises and args of the current conclusion to the vector of premises and args of the new conclusion
                    args = ps.args.clone();
                    for &prem in &ps.premises{
                        if prem.0 == depth {
                            let commands: &Vec<ProofCommand> = &p.part_commands;
                            let local_position: usize = p.local_index_of(prem, sub_adrs);
                            let command: &ProofCommand = &commands[local_position];
                            let (command, location): (&ProofCommand, (usize,usize)) = p.resolve_substitute(command, prem);
                            premises.push(Premise::new(location,command));
                        } else {
                            let new_sub: Option<usize> = self.stalk_owner(sub_adrs, prem.0);
                            let fixed: &HashMap<(usize, usize), Option<(usize, usize)>> = self.get_current_fix(new_sub);
                            match fixed.get(&prem){
                                Some(&Some(location)) => {
                                    let command = cache.get(location);
                                    premises.push(Premise::new(location,command));
                                }
                                _ => panic!("An outer premise should be listed as a fixed step in its proof level"),
                            };
                                //get new position of (command_depth, prem_loc) in cache[command_depth]
                            
                            
                        };
                    }
                    
                    // Now the premises and arguments for the collected clauses will be added
                    for (i, old_location) in queue.iter().enumerate(){
                        let location: (usize, usize) = self.get_new_index_of_outer_premise(sub_adrs, *old_location);
                        let unary_local_ind: usize = queue_local[i];
                        let unary_step: &ProofCommand = &p.part_commands[unary_local_ind];
                        let (_, location): (&ProofCommand, (usize,usize)) = p.resolve_substitute(unary_step, location);
                        let local_position: usize = p.local_index_of(location, sub_adrs);
                        let new_premise = Premise::new(location,&p.part_commands[local_position]);
                        premises.push(new_premise);
                    }
                    
                    for (lit, polarity) in args_queue{
                        args.push(lit.clone());
                        args.push(polarity.clone());
                    }
                } else {
                    panic!("The conclusion of a compressible part should not be an assume nor a subproof.")
                }
                
                let resolution: ResolveResult = Self::resolve_when_possible(&premises, &args, proof_pool);
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
            match pt.parts[ind].part_commands.first_mut(){
                Some(com) => {
                    *com = conc;
                },
                _ => panic!("If this part is empty, how was a new conclusion computed?"),
            }
            pt.parts[ind].compressed = true;
        }
        let elapsed = now.elapsed();
        elapsed
    }

    fn rebuild(&mut self, pt: &mut PartTracker, sub_adrs: Option<usize>) -> (Duration, Vec<ProofCommand>){
        let now = Instant::now();
        let depth: usize = self.get_depth(sub_adrs);
        let mut a_count: usize = 0;
        let mut t_count: usize = 0;
        let base_string: String = self.get_base_id(sub_adrs);

        //maps original index into the index of the proof being constructed
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
                    term: a.clause()[0].clone()
                };
                let mut part_table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
                ProofCompressor::insert_command_on_new_proof(
                                            &mut new_commands,
                                                            com,
                                                            &mut table,
                                                            index,
                                                            depth,
                                                            &pt.parts[0],
                                                            &mut part_table
                                                        );
                a_count+=1;
                discharge.push((depth,i));

            }
            if depth==0{
                premises.insert(a.clause()[0].clone());
            }
        }
        match sub_adrs {
            None => (),
            Some(v) => self.subproofs[v].discharge = discharge,
        }
        for part in pt.parts[1..].iter().rev(){
            //maps original index into the index of the proof being constructed, 
            //but only has keys for steps that were recomputed in the current part
            let mut part_table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
            for (i, c) in part.part_commands.iter().enumerate().rev(){
                let index = part.original_index[i];
                if  (!table.contains_key(&index)               ||  // ensures it was not already added in the proof   
                     part.is_recomputed(index))                &&  // or, if it was added, this part version was recomputed
                    !part.marked_for_deletion.contains(&index) &&  // ensures it is not substituted
                    index.0==depth
                {
                    let mut com = c.clone();
                    match &mut com{ //update 
                        ProofCommand::Assume{..} => (),
                        ProofCommand::Step(ps) => {
                            if !self.sp_binder.contains(&ps.rule){
                                self.update_vec(index,&mut ps.premises, &table, sub_adrs, part, &mut part_table);
                                ps.id = format!("{}t{:?}", &base_string, t_count);
                                t_count+=1;
                            }
                        }
                        ProofCommand::Subproof(sp_ph) => {
                            let id = sp_ph.context_id;
                            self.subproofs[id].new_ind = new_commands.len();
                            if let ProofCommand::Step(ps) = sp_ph.commands.last().expect("There should be no empty subproofs"){
                                let mut ps_c = ps.clone();
                                self.update_vec(index,&mut ps_c.premises, &table, sub_adrs, part, &mut part_table);
                                ps_c.id = format!("{}t{:?}", &base_string, t_count);
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
                                        depth,
                                        part,
                                        &mut part_table
                                    );
                }
            }
        }
        self.fill_fixed(table,sub_adrs);
        let elapsed = now.elapsed();
        (elapsed, new_commands)
    }

    fn get_depth(&self, sub_adrs: Option<usize>) -> usize {
        match sub_adrs{
            Some(v) => self.subproofs[v].depth,
            None => 0,
        }
    }

    fn rebuild_verbose(&mut self, pt: &mut PartTracker, sub_adrs: Option<usize>) -> Vec<ProofCommand>{
        if sub_adrs.is_none(){
            println!();
            println!("Rebuilding from here");
        }
        let depth: usize = self.get_depth(sub_adrs);
        let mut a_count: usize = 0;
        let mut t_count: usize = 0;
        let base_string: String = self.get_base_id(sub_adrs);

        //maps original index into the index of the proof being constructed
        let mut table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
        
        let mut premises: IndexSet<Rc<Term>> = IndexSet::new();
        let mut discharge: Vec<(usize,usize)> = vec![];
        let mut new_commands: Vec<ProofCommand> = vec![];
        
        let assumes: &Vec<ProofCommand> = &pt.parts[0].part_commands;
        let n = assumes.len();
        // Builds the premises field and insert the assumes in the proof
        for (i, a) in assumes.iter().rev().enumerate(){
            let index: (usize, usize) = pt.parts[0].original_index[n-i-1];
            if sub_adrs.is_none(){
                println!();
                println!("On part 0 I see {:?}:{:?} - {:?}",a.id(),index,a.clause());
            }
            if depth==index.0{
                let com = ProofCommand::Assume {
                    id: format!("{}a{:?}", &base_string, a_count), 
                    term: a.clause()[0].clone()
                };
                let mut part_table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
                self.insert_command_on_new_proof_verbose(
                                              &mut new_commands,
                                                        com,
                                                        &mut table,
                                                        (index, sub_adrs),
                                                        &pt.parts[0],
                                                        &mut part_table,
                                                    );
                a_count+=1;
                discharge.push((depth,i));

            }
            if depth==0{
                premises.insert(a.clause()[0].clone());
            }
        }
        if sub_adrs.is_none(){
            println!("__________________________________________________________");
        }
        match sub_adrs {
            None => (),
            Some(v) => self.subproofs[v].discharge = discharge,
        }
        for part in pt.parts[1..].iter().rev(){
            //maps original index into the index of the proof being constructed, 
            //but only has keys for steps that were recomputed in the current part
            let mut part_table: HashMap<(usize,usize),(usize,usize)> = HashMap::new();
            for (i, c) in part.part_commands.iter().enumerate().rev(){
                let index: (usize, usize) = part.original_index[i];
                if sub_adrs.is_none(){
                    println!();
                    println!("On part {:?} I see {:?}:{:?} - {:?}", part.ind, c.id(), index, c.clause());
                    if table.contains_key(&index) && !part.is_recomputed(index){
                        println!("Will not enter because the key is inside the table and this version of the step was not recomputed");
                    }
                    if part.marked_for_deletion.contains(&index){
                        println!("Will not enter because is marked to substitution on part {:?}",part.ind);
                    }
                    if index.0!=depth{
                        println!("Will not enter because this step is from another level");
                    }
                }
                
                if  (!table.contains_key(&index)               ||  // ensures it was not already added in the proof   
                     part.is_recomputed(index))                &&  // or, if it was added, this part version was recomputed
                    !part.marked_for_deletion.contains(&index) &&  // ensures it is not substituted
                    index.0==depth
                {   
                    if sub_adrs.is_none(){
                        println!("entered");
                    }
                    let mut com = c.clone();
                    match &mut com{ //update 
                        ProofCommand::Assume{..} => (),
                        ProofCommand::Step(ps) => {
                            if !self.sp_binder.contains(&ps.rule){
                                if sub_adrs.is_none(){
                                    println!("Now on {:?}:{:?} we will substitute its premises",c.id(), index);
                                    println!("Old: {:?}",&ps.premises);
                                }
                                self.update_vec(index, &mut ps.premises, &table, sub_adrs, part, &mut part_table);
                                if sub_adrs.is_none(){
                                    println!("New: {:?}",&ps.premises);
                                }
                                ps.id = format!("{}t{:?}", &base_string, t_count);
                                t_count+=1;
                            }
                        }
                        ProofCommand::Subproof(sp_ph) => {
                            let id = sp_ph.context_id;
                            self.subproofs[id].new_ind = new_commands.len();
                            if let ProofCommand::Step(ps) = sp_ph.commands.last().expect("There should be no empty subproofs"){
                                let mut ps_c = ps.clone();
                                self.update_vec(index, &mut ps_c.premises, &table, sub_adrs, part, &mut part_table);
                                ps_c.id = format!("{}t{:?}", &base_string, t_count);
                                com = ProofCommand::Step(ps_c);
                                t_count+=1;
                            }

                        }
                    }
                    self.insert_command_on_new_proof_verbose(
                          &mut new_commands,
                                    com,
                                    &mut table,
                                    (index, sub_adrs),
                                    part,
                                    &mut part_table,
                                    );
                }
            }
        }
        if sub_adrs.is_none(){
            println!("__________________________________________________________");
        }
        self.fill_fixed(table,sub_adrs);
        new_commands
    }

    fn update_vec(
        &self,
        index: (usize, usize),
        v: &mut [(usize,usize)], 
        table: &HashMap<(usize,usize),(usize,usize)>, 
        sub_adrs: Option<usize>, 
        part: &DisjointPart,
        part_table: &mut HashMap<(usize,usize),(usize,usize)>
    ){
        for prem in v.iter_mut() {
            if part.is_recomputed(*prem){
                if let Some(updt_prem) = part_table.get(prem) {
                    *prem = *updt_prem;
                }
            } else if let Some(updt_prem) = table.get(prem){
                *prem = *updt_prem;
            } else if !part.is_recomputed(index){
                *prem = self.get_new_index_of_outer_premise(sub_adrs, *prem);
            }
        }
    }

    fn fill_fixed(&mut self, table: HashMap<(usize,usize),(usize,usize)>, sub_adrs: Option<usize>){
        let fixed: &mut HashMap<(usize, usize), Option<(usize, usize)>> = match sub_adrs{
            None => &mut self.fixed,
            Some(v) => &mut self.subproofs[v].fixed,
        };
        for (old_ind, destination) in fixed.iter_mut() {
            let new_ind: (usize, usize) = table[old_ind];
            *destination = Some(new_ind);
        }
    }

    fn get_new_index_of_outer_premise(&self, sub_adrs: Option<usize>, old_ind: (usize,usize))-> (usize,usize){
        let outer: &HashMap<usize, (Vec<usize>, Option<usize>)> = match sub_adrs{
            None => &self.outer,
            Some(v) => &self.subproofs[v].outer,
        };

        let op = match outer.get(&old_ind.0){
            Some((_, None)) => self.fixed[&old_ind],
            Some(&(_, Some(v))) => self.subproofs[v].fixed[&old_ind],
            None => Some(old_ind)
        };
        match op{
            Some(new_index) => new_index,
            None => old_ind,
        }
    }

    fn insert_command_on_new_proof(
        new_proof: &mut Vec<ProofCommand>, 
        com: ProofCommand, 
        table: &mut HashMap<(usize,usize),(usize,usize)>,
        index: (usize,usize), 
        depth: usize,
        part: &DisjointPart,
        part_table: &mut HashMap<(usize,usize),(usize,usize)>
    ){
        let n = new_proof.len();
        // This command can be used as premise of commands from other parts if, and only if it was not recomputed or if it is
        // The conclusion of a part. This is because the part conclusions are recomputed to yield the same value they had before
        // the compression
        if !part.is_recomputed(index) || part.original_index[0]==index{      
            table.insert(index,(depth,n));
        } else {
            part_table.insert(index, (depth,n));
        }
        new_proof.push(com);
    }

    fn insert_command_on_new_proof_verbose(
        &self,
        new_proof: &mut Vec<ProofCommand>, 
        com: ProofCommand, 
        table: &mut HashMap<(usize,usize),(usize,usize)>,
        index_sub_adrs: ((usize,usize), Option<usize>), 
        part: &DisjointPart,
        part_table: &mut HashMap<(usize,usize),(usize,usize)>,
    ){
        let index: (usize, usize) = index_sub_adrs.0;
        let sub_adrs: Option<usize> = index_sub_adrs.1;
        let depth: usize = self.get_depth(sub_adrs);
        let n = new_proof.len();
        if part.is_recomputed(index){
            if sub_adrs.is_none(){
                println!("Here, {:?} was locally (p{:?}) mapped to {:?}",index,part.ind,(depth,n));    
            }
            part_table.insert(index, (depth,n));
        } else {
            if sub_adrs.is_none(){
                println!("Here, {:?} was globally mapped to {:?}",index,(depth,n));
            }
            table.insert(index,(depth,n));
        }
        new_proof.push(com);
    }

    fn position_insert(&mut self, new_commands: Vec<ProofCommand>, sub_adrs: Option<usize>){
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
        let adrs_depth: usize = self.get_depth(sub_adrs);
        if step.0 == 0{
            commands = &self.proof.commands;
        } else if adrs_depth == step.0{
            commands = self.dive_into_proof(sub_adrs);
        } else {
            let owner = self.stalk_owner(sub_adrs, step.0).unwrap();
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
                        &self.subproofs[self.stalk_owner(sub_adrs, depth).unwrap()].proof.commands
                    }
                }
            };
            let rule = commands[ind].rule();
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
    
    fn re_contract(&mut self, 
        part: &mut DisjointPart, 
        index: usize,
        sub_adrs: Option<usize>
    ){
        let premises = part.part_commands[index].premises();
        let parent_global_ind = premises[0];
        let parent_local_ind = part.local_index_of(parent_global_ind, sub_adrs);
        let parent_clause: Vec<Rc<Term>> = 
            part.part_commands[parent_local_ind]
            .clause()
            .to_vec();
        let clause_set: IndexSet<Rc<Term>> = parent_clause.into_iter().collect();
        let new_contract: Vec<Rc<Term>> = clause_set.into_iter().collect();
        let to_compress = &mut part.part_commands[index];
        self.overwrite_clause(to_compress, new_contract);
        
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
        proof_pool: &mut PrimitivePool,
    ) -> 
    ReResolveReturn{
        let mut remaining: Vec<(usize, usize)> = part.remaining_premises(index);
        let table: &HashMap<(usize, usize), (usize, usize)> = &part.subs_table;
        let mut new_commands: Vec<(ProofCommand,(usize,usize))> = Vec::new();
        let mut premises: Vec<Premise<'_>> = self.build_premises(part, &remaining, index, sub_adrs, &mut new_commands);
        let args = Self::build_args(part, &remaining, index);
        for r in &mut remaining{
            if let Some(rr) = table.get(r) {
                let aft_subs = self.get_new_index_of_outer_premise(sub_adrs, *rr);
                for p in &mut premises{
                    if p.index==*r{        
                        p.index = aft_subs;
                        let local_ind: usize = part.local_index_of(aft_subs, sub_adrs);
                        p.clause = part.part_commands[local_ind].clause();
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
                    ReResolveReturn{
                        clause: resolvent,
                        premises: formatted_premises, 
                        args: vec![]
                    }
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
                    ReResolveReturn{
                        clause: resolvent,
                        premises: formatted_premises, 
                        args
                    }
                    
                }
                _ => {
                    eprintln!("Error: Clauses couldn't be resolved on {:?}", sub_adrs);
                    eprintln!("Resolving for {:?} on part {:?}", index, part.ind);
                    eprintln!("Premises {:?}", &premises);
                    eprintln!("Premises indexes {:?}", premises.iter().map(|x| x.index).collect::<Vec<_>>());
                    panic!("Arguments: {:?}", args);
                    }
            }
        }
    }

    fn build_premises(&'a self,
        part: &DisjointPart, 
        remaining: &[(usize, usize)], 
        index: usize, 
        sub_adrs: Option<usize>, 
        new_commands: &'a mut Vec<(ProofCommand,(usize,usize))>
    ) -> Vec<Premise<'a>>{
        let depth: usize = self.get_depth(sub_adrs);
        let mut cache: ProofCache<'_> = ProofCache::new(self, sub_adrs);
        let mut ans: Vec<Premise> = vec![];
        let data = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().copied().collect();
        let premises: &Vec<(usize, usize)> = data.premises();
        for &prem in premises{
            if remaining_set.contains(&prem){
                let new_comm: ProofCommand;
                let correct_prem: (usize, usize) =
                    if prem.0==depth{
                        prem
                    } else {
                        self.get_new_index_of_outer_premise(sub_adrs, prem)
                    };
                let local: usize = part.local_index_of(correct_prem, sub_adrs);
                let local_command = &part.part_commands[local];
                match cache.get(correct_prem){
                    ProofCommand::Assume { id, .. } => 
                    new_comm = ProofCommand::Assume{id: id.clone(),
                                                    term: local_command.clause()[0].clone() 
                                                    },
                    ProofCommand::Step(ps) => {
                        let mut ps_temp = ps.clone();
                        ps_temp.clause = local_command.clause().to_vec();
                        new_comm = ProofCommand::Step(ps_temp);
                    }
                    ProofCommand::Subproof(ph_sp) => {
                        let sp = self.access_subproof(ph_sp);
                        let sub_conclusion = sp.commands.last().unwrap();
                        if let ProofCommand::Step(ps) = sub_conclusion{
                            let mut ps_temp = ps.clone();
                            ps_temp.clause = local_command.clause().to_vec();
                            new_comm = ProofCommand::Step(ps_temp);
                        } else {
                            panic!("The last element of a subproof should be a Step");
                        }
                    }
                }
                new_commands.push((new_comm,correct_prem));
            
        }
        }
        for (c,loc) in new_commands.iter(){
            ans.push(Premise::new(*loc,c));
        }
        ans
    }    

    fn build_args(part: &DisjointPart, remaining: &[(usize, usize)], index: usize) -> Vec<Rc<Term>>{ // ok
        let mut ans: Vec<Rc<Term>> = vec![];
        let comm = &part.part_commands[index];
        let remaining_set: HashSet<_> = remaining.iter().copied().collect();
        let old_args = comm.args(); 
        let premises: &Vec<(usize, usize)> = comm.premises();
        let n: usize = if remaining_set.contains(&premises[0]) {1} else {2};
        for (i, &p) in premises.iter().enumerate().skip(n){
            if remaining_set.contains(&p){
                ans.push(old_args[2*i-2].clone());
                ans.push(old_args[2*i-1].clone());
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

    fn is_pseudo_assume(&self, step: (usize, usize), commands: &[ProofCommand] ,sub_adrs: Option<usize>) -> bool{
        match &commands[step.1]{
            ProofCommand::Step(ps) => {
                if ps.premises.len()==1{
                    let prem = ps.premises[0];
                    if prem.0==step.0{
                        commands[prem.1].is_assume()
                    } else if prem.0==0{
                        self.proof.commands[prem.1].is_assume()
                    } else {
                        let ind = self.stalk_owner(sub_adrs, prem.0).unwrap();
                        self.subproofs[ind].proof.commands[prem.1].is_assume()
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn reassemble(&'a mut self, mut stats: Option<&'b mut CompressorStatistics>)->Option<&'b mut CompressorStatistics>{
        let n: usize = self.subproofs.len();
        let mut compressed_size = 0;
        let mut subproof_meta: Vec<SubproofMeta> = mem::take(&mut self.subproofs);
        for sub_ind in (0..n).rev(){
            compressed_size += subproof_meta[sub_ind].proof.commands.len();
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

            // The step with the subproof conclusion was adjusted at the parent level
            // I.e., the subproof at depth 3 was adjusted while running the algorithm at level 2
            // This operation puts the adjusted conclusion
            mem::swap(&mut commands[new_ind], sub.commands.last_mut().unwrap());
            commands[new_ind] = ProofCommand::Subproof(sub);
        }
        compressed_size+=self.proof.commands.len();
        if let Some(S) = stats{
            S.final_size = Some(compressed_size);
            Some(S)
        } else {
            None
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

    fn tidy_up_outer_dependencies(&mut self, prem: (usize, usize), sub_adrs: Option<usize>){
        let adrs: usize = sub_adrs.expect("This must be dead code, as the first proof level will never be realocated");
        let owner_op: Option<usize> = self.stalk_owner(sub_adrs, prem.0);
        let fixed: &mut HashMap<(usize,usize),Option<(usize,usize)>> = match owner_op{
            None => &mut self.fixed,
            Some(owner) => &mut self.subproofs[owner].fixed,
        };
        fixed.insert(prem,None);
        self.insert_or_append_to_outer(adrs, prem, owner_op);
    }

    fn insert_or_append_to_outer(&mut self, adrs: usize, prem: (usize, usize), prem_own_addrss: Option<usize>){
        match self.subproofs[adrs].outer.get_mut(&prem.0){
            Some((v,_)) => v.push(prem.1),
            None => {
                self.subproofs[adrs].outer.insert(prem.0,(vec![prem.1],prem_own_addrss));
            }
        }
    }

    fn implicit_premises(&self, command: &ProofCommand, src_depth: usize) -> Vec<(usize, usize)>{
        if let ProofCommand::Subproof(sp) = command{
            let set: IndexSet<(usize, usize)> = self.recursively_implicit_premises(sp.context_id, src_depth);
            set.iter().copied().collect()
        } else {
            panic!("Implicit premises should only be called for subproofs")
        }
    }

    fn print_part(&self, part: &DisjointPart){
        println!("Part {:?}", part.ind);
        for (i, com) in part.part_commands.iter().enumerate(){
            match com{
                ProofCommand::Assume { id, term } => println!("{:?}; {:?} - Assume {:?}: {:?}",i,part.original_index[i],id,term),
                ProofCommand::Step(ps) => 
                println!("{:?}; {:?} - Step {:?} {:?}: {:?}; prem: {:?}; arg: {:?}", i, part.original_index[i], &ps.id,&ps.rule,&ps.clause,&ps.premises, &ps.args),
                ProofCommand::Subproof(sp_ph) => {
                    let sp = self.access_subproof(sp_ph);
                    match sp.commands.last(){
                        None => panic!("empty"),
                        Some(ProofCommand::Step(ps)) => println!("{:?}; {:?} - Sub {:?} {:?}: {:?}; prem: {:?}; disc: {:?}", i, part.original_index[i], &ps.id,&ps.rule,&ps.clause,&ps.premises, &ps.discharge),
                        _ => panic!("Not a proofstep")
                    };
                }
            }
        }
    }
    
    fn resolve_when_possible( 
        premises: &[Premise<'a>], 
        args: &'a [Rc<Term>], 
        pool: &mut PrimitivePool,
    ) -> ResolveResult<'a>{
        
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
            if result.is_err(){
                useless_premise.push(i+1);
            }
        }
        Ok((current, useless_premise))
    }

    //returns true if, and only if the compressible parts of this command can be expanded from this point
    fn internal_command(&self, ps: &ProofStep, sub_adrs: Option<usize>) -> bool{
        ps.rule == "resolution" || 
        ps.rule == "th-resolution" || 
        (self.preserving_binder.contains(&ps.rule) && self.resolution_is_a_premise(ps, sub_adrs))
    }

    fn is_resolution_or_pseudo(&self, c: &ProofCommand, sub_adrs: Option<usize>) -> bool{
        match c{
            ProofCommand::Step(ps) => self.internal_command(ps, sub_adrs),
            _ => false
        }
    }
}


fn print_proof(p: &[ProofCommand], indentation: String, base: usize, depth: usize) -> usize{
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
                let mut s: String = format!("{}{} - {} {}: {:?}", &indentation, from+i, &ps.id, &ps.rule, &ps.clause);
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
                let op = format!("{}Opening subproof, id: {}, args: {:?}", &indentation, &sp.context_id, &sp.args);
                println!("{:?}",&op);
                let new_indentation = indentation.clone() + "   ";
                sub_len = print_proof(&sp.commands, new_indentation, i+from, depth+1);
                from += sub_len;
                match sp.commands.last(){
                    None => panic!("Empty subproof at printer"),
                    Some(ProofCommand::Step(ps)) => {
                        let mut s: String = format!("{}{} - {} {}: {:?}", &indentation, from+i, &ps.id, &ps.rule, &ps.clause);
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

pub struct ProofCache<'a>{
    mem: Vec<&'a Vec<ProofCommand>>,
    address: Option<usize>,
    compressor: &'a ProofCompressor,
}

impl<'a> ProofCache<'a>{
    pub fn new(compressor: &'a ProofCompressor, sub_adrs: Option<usize>) -> ProofCache<'a>{
        static EMPTY_ENTRY: Vec<ProofCommand> = vec![];
        let depth = compressor.get_depth(sub_adrs);
        let mut cache = ProofCache{
            mem: vec![&EMPTY_ENTRY;depth+1],
            address: sub_adrs,
            compressor,
        };
        cache.mem[depth] = compressor.dive_into_proof(sub_adrs);
        cache
    }

    pub fn get(&mut self, ind: (usize, usize)) -> &'a ProofCommand {
        if self.mem[ind.0].is_empty(){
            self.load(ind.0);
        }
        &self.mem[ind.0][ind.1]
    }

    pub fn load(&mut self, parent_depth: usize){
        let parent_address = self.compressor.stalk_owner(self.address, parent_depth);
        self.mem[parent_depth] = self.compressor.dive_into_proof(parent_address);
    }

    pub fn level_is_empty(&self, level: usize) -> bool{
        self.mem[level].is_empty()
    }
}