//Task: write general version of lower units in Latex using an abstraction level of the same level as the original article.
//Important: Never modify a proof more than needed

//OPT: Implement reinsert_units_parted with at maximum one resolution for each part
//OPT: The PartTracker vectors can use less space if split in two variables
//OPT: write lifetime anotations to make found_clauses use references as keys in rebuild_parted
//WARN: assume after steps
//Task: Try to create an example where the collected unit is a subproof
//Task: Create an example where the last step isn't resolution

//nome alethe novo, artigos e acesso
use crate::ast::*;
use std::collections::{HashSet, HashMap};
use std::ops::Index;
use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
use indexmap::{IndexMap, IndexSet};
use std::env;
mod error;
use crate::compressor::error::CompressionError;

#[derive(Debug)]
pub struct ProofCompressor{
    pub proof: Proof,
    not_delete: HashSet<Rc<Term>>,
    sp_binder: HashSet<&'static str>
}

#[derive(Debug)]
pub struct ClauseData{
    index: Option<(usize,usize)>,
    data: ProofCommand,
    local_premises: Vec<usize>
}






#[derive(Debug, Clone, Default)]
pub struct PartTracker{
    data: HashMap<usize,usize>,
    inv_index: HashMap<usize,usize>
}

impl PartTracker{
    fn new()->PartTracker{
        PartTracker{
            data: HashMap::new(),
            inv_index: HashMap::new()
        }
    }

    fn new_insert(u: usize)->PartTracker{
        let mut pt = PartTracker{
            data: HashMap::new(),
            inv_index: HashMap::new()
        };
        pt.insert(u);
        pt
    }

    fn insert(&mut self, a: usize) -> (){
        if self.data.contains_key(&a){
            *self.data.entry(a).or_insert(0) += 1;
        } else {
            self.data.insert(a,1);
        }
    }

    fn register(&mut self, part_ind: usize, ind: usize)->(){
        self.inv_index.insert(part_ind,ind);
    }
}

pub fn print_subproof(sp: &Subproof, depth: Option<usize>) -> (){
    println!("Assigment args:\n{:?}",sp.assignment_args);
    println!("Variable args:\n{:?}",sp.variable_args);
    println!("Context id: {:?}",sp.context_id);
    println!("Commands:");
    match depth{
        None => {
            for c in sp.commands.iter().enumerate(){
                match c.1{
                    ProofCommand::Assume { id, term } => println!("{} - assume {}: {:?}", c.0, id, term),
                    ProofCommand::Step(ps) => println!("{} - {} {}:\n {:?} -> {:?}", c.0, ps.rule, ps.id, ps.premises, ps.clause),
                    ProofCommand::Subproof(sp) => print_subproof(sp, Some(1))
                }
            }
        }
        Some(d) => {
            for c in sp.commands.iter().enumerate(){
                match c.1{
                    ProofCommand::Assume { id, term } => println!("{}.{} - assume {}: {:?}", d, c.0, id, term),
                    ProofCommand::Step(ps) => println!("{}.{} - {} {}:\n {:?} -> {:?}", d, c.0, ps.rule, ps.id, ps.premises, ps.clause),
                    ProofCommand::Subproof(sp) => print_subproof(sp,Some(d+1))
                }
            }
        }
    }
}

pub fn print_part(part: &Vec<ClauseData>, part_n: Option<usize>)->(){
    match part_n{
        Some(j) => println!("Parte {j}"),
        None => ()
    }
    for i in 0..part.len(){
        println!("{:?} - Index: {:?}",i,part[i].index);
        match &part[i].data{
            ProofCommand::Assume { term,.. } => println!("Clause: {:?}\n", term),
            ProofCommand::Step(ps) => {
                println!("Clause: {:?}", &ps.clause);
                println!("Local Premises: {:?}", &part[i].local_premises);
                println!("Global Premises: {:?}\n", &ps.premises);
            },
            _ => ()
        }
    }
}


impl ProofCompressor{
    pub fn new(p: &Proof)->ProofCompressor{
        ProofCompressor{
            proof: p.clone(),
            not_delete: HashSet::new(),
            sp_binder: HashSet::from_iter(vec!["subproof","let","sko_ex","sko_forall","bind","onepoint"].into_iter())
        }
    }


    fn substitute_node_by_parent(
        ind: usize,
        unitary_parent_ind: usize,
        substituted: &mut HashMap<usize,usize>
    ) -> (){
        //println!("Pointing {:?} by {:?}",ind,unitary_parent_ind);
        //println!("Map: {:?}",substituted);
        let mut substitute = unitary_parent_ind;
        if substituted.contains_key(&substitute){
            substitute = *substituted.get(&substitute).unwrap();
        }
        substituted.insert(ind, substitute);
    }

    fn select_args(
        not_missing: &Vec<(usize,usize)>,
        args: &Vec<ProofArg>
    )-> Option<Vec<ProofArg>>{
        //println!("nm: {:?}", not_missing);
        //println!("args: {:?}", args);
        let not_missing_set: IndexSet<_> = not_missing.iter().map(|(f, _)| *f).collect();
        let param_num = args.len()/2+1;
        //println!("param_num {param_num}");
        let mut args_to_ignore: IndexSet<usize> = IndexSet::new();
        //println!("nms: {:?}",&not_missing_set);
        if !not_missing_set.contains(&0){
            args_to_ignore.insert(0);
            args_to_ignore.insert(1);
        }
        for i in 1..param_num{
            if !not_missing_set.contains(&i){
                args_to_ignore.insert((i-1)*2);
                args_to_ignore.insert((i-1)*2+1);
            }
        }
        //println!("argstoig: {:?}", &args_to_ignore);
        let mut selected = vec![];
        for i in 0..args.len(){
            if !args_to_ignore.contains(&i){
                selected.push(args[i].clone());
            }
        }
        //println!("selected: {:?}",&selected);
        Some(selected)
    }

//-i --allow-int-real-subtyping --expand-let-bindings
    pub fn run_compressor(&mut self, _pool: &mut PrimitivePool) -> Proof{
        env::set_var("RUST_BACKTRACE", "1");
        let mut outer_steps: &mut IndexMap<Vec<usize>,IndexSet<(usize,usize)>> = &mut IndexMap::new();
        match self.compress(&None, outer_steps, _pool){
            Err(e) => {
                match e{
                    //CompressionError::Collection(_) => println!("There is no collectable clauses."),
                    CompressionError::SubproofNotImplementedYet => (),//println!("The logic to compress subproofs is yet to be implemented."),
                    CompressionError::ResolutionError(res) => println!("There was an error when resolving the clauses {:?}.",res),
                }
            }
            Ok(()) => ()
        }
        self.proof.clone()
    }

    
    pub fn compress(&mut self, sub: &Option<Vec<usize>>, outer_steps: &mut IndexMap<Vec<usize>,IndexSet<(usize,usize)>>, _pool: &mut PrimitivePool) -> Result<(),CompressionError>{
        //self.print();
        let mut none_flag = false;
        let (mut parts, 
            part_deleted,
            part_units_queue,
            referenced_by_parts) = self.collect_units(sub, outer_steps, _pool);
        /*let substituted_in_parts = self.fix_broken_proof(
            part_deleted,
            &mut parts,
            depth,
            _pool
        )?;
        self.reinsert_units(&mut parts, part_units_queue, &substituted_in_parts, referenced_by_parts, _pool);
        self.rebuild(substituted_in_parts,parts,sub);
        sp = subproofs_to_compress;*/
        
        Ok(())
    }
    

    
    // Iterates over the proof
    // Since a generic proof may have any kind of rule and our algorithm is valid just for resolution rules,
    // while iteratig over the proof the function search for connected parts of the proof that uses only resolution
    // and at the same time, counts how many time each clause is used in each parts.
    // Each part has an associated queue and whenever an unitary clause is used as premise for a resolution step 2 or more times inside a part,
    // this clause is added to that part's queue.
    
    // Returns:
    // parts: A vector, each element is a vector of clauses with additional data. The idea is that every element of this part 
    // work as a connected part with resolutions only, the data itself looks like a local snapshot of the proof
    // view of the proof. The additional date purpose is reconstruct the proof later and map each clause from the part into
    // a node of the commands vector from the proof.

    // part_deleted: A vector of sets, the i-th set contains the nodes that must be deleted in part i. This variable exists to
    // check if a clause should be deleted in O(1)

    // part_units_queue: A vector of vectors. The i-th element of this variable is a vector representing the units queue 
    // from the i-th part

    // referenced_by_parts: HashMap of PartTrackers, key (d, i) stores all parts that contain the node (d, i) and how many times
    // this node is used inside that part
    pub fn collect_units(&mut self, sub: &Option<Vec<usize>>, outer_steps: &mut IndexMap<Vec<usize>,IndexSet<(usize,usize)>>, _pool: &mut PrimitivePool)->
        (Vec<Vec<ClauseData>>,
        Vec<HashSet<(usize,usize)>>,
        Vec<Vec<(usize,usize)>>,
        HashMap<(usize,usize),PartTracker>)
    {
        let mut to_compress: Vec<Vec<usize>> = vec![];
        
        let mut adrs = vec![];
        let mut depth = 0;
        //self.print();
        let mut parts: Vec<Vec<ClauseData>> = vec![Vec::new(),Vec::new()];
        let mut referenced_by_parts: HashMap<(usize,usize),PartTracker> = HashMap::new();

        
        let mut part_units_queue: Vec<Vec<(usize,usize)>> = vec![Vec::new(),Vec::new()];
        let mut part_deleted: Vec<HashSet<(usize,usize)>> = vec![HashSet::new(),HashSet::new()];
        let mut coming_from_resolution: HashSet<(usize,usize)> = HashSet::new();
        let mut compress_later: IndexSet<Vec<usize>> = IndexSet::new();
        {
            let mut commands = &self.proof.commands;
            match sub{
                Some(addrs) => {
                    adrs = addrs.clone();
                    commands = self.get_subproof_commands(&adrs);
                }
                None => ()
            }
            depth = adrs.len();
            let n = commands.len();
            //anotates the conclusion of the commands vector on part 1
            //part 0 is reserved for assumes
            referenced_by_parts.insert((depth,n-1), PartTracker::new_insert(1));
            for i in (0..commands.len()).rev(){
                let pc = &commands[i];
                match pc{
                    ProofCommand::Assume{id, term} => {
                        let mut current_parts: &mut PartTracker;
                        match referenced_by_parts.get_mut(&(depth,i)) {
                            Some(value) => current_parts = value,
                            None => {
                                current_parts = &mut PartTracker::new();
                                panic!("({depth},{i}) is not referenced by any part");
                            }
                        }
                        for (&k, &times) in &current_parts.data{
                            if times>=2{
                                part_units_queue[k].push((depth,i));
                                part_deleted[k].insert((depth,i));
                            }
                            
                            current_parts.inv_index.insert(k,parts[k].len());
                            parts[k].push(ClauseData{
                                index: Some((depth,i)),
                                data: ProofCommand::Assume{id: id.to_string(), term: term.clone()},
                                local_premises: vec![]
                            });
                        }
                        current_parts.register(0, parts[0].len());
                        parts[0].push(ClauseData{
                            index: Some((depth,i)),
                            data: ProofCommand::Assume{id: id.to_string(), term: term.clone()},
                            local_premises: vec![]
                        });
                    }

                    ProofCommand::Step(ps) => {
                        let is_resolution = ps.rule=="resolution"||ps.rule=="th-resolution";
                        if is_resolution{  
                            self.collecting_resolutions(
                                depth, 
                                i,
                                sub, 
                                &mut referenced_by_parts, 
                                &mut coming_from_resolution,
                                &mut part_units_queue,
                                &mut part_deleted,
                                &mut parts,
                                outer_steps,
                                ps
                            );
                        } else { //is not a resolution
                            if coming_from_resolution.contains(&(depth,i)){//not a resolution but a premise of a resolution
                                self.collecting_resolution_premises(
                                    depth, 
                                    i,
                                    sub, 
                                    &mut referenced_by_parts, 
                                    &mut coming_from_resolution,
                                    &mut part_units_queue,
                                    &mut part_deleted,
                                    &mut parts,
                                    outer_steps,
                                    ps
                                );
                            } else { 
                                //not a resolution nor premise of a resolution
                                self.not_resoltion_nor_premises(
                                    depth, 
                                    i,
                                    &mut referenced_by_parts, 
                                    &mut parts,
                                    ps
                                );
                            }
                        }
                    }
                    ProofCommand::Subproof(sp) => {
                        let mut adrs_sp = adrs.clone();
                        adrs_sp.push(i);
                        compress_later.insert(adrs_sp);
                        let last_clause = self.subproof_conclusion(&Some(adrs.clone()));
                        let conclusion = &last_clause.clause;
                        let resumed_to_step = 
                        ProofStep {
                            id: last_clause.id.clone(), 
                            clause: conclusion.clone(), 
                            rule: last_clause.rule.clone(), 
                            premises: last_clause.premises.clone(), 
                            args: last_clause.args.clone(), 
                            discharge: last_clause.discharge.clone()
                        };

                        let mut current_parts: &mut PartTracker;
                        match referenced_by_parts.get_mut(&(depth,i)) {
                            Some(value) => current_parts = value,
                            None => {
                                current_parts = &mut PartTracker::new();
                                panic!("({depth},{i}) is not referenced by any part");
                            }
                        }
                        for (&k, &times) in &current_parts.data{    
                            parts[k].push(ClauseData{
                                index: Some((depth,i)),
                                data: ProofCommand::Step(resumed_to_step.clone()),
                                local_premises: vec![]
                            });
                        
                            if coming_from_resolution.contains(&(depth,i)) && times>=2 && conclusion.len()==1{
                                part_units_queue[k].push((depth,i));
                                part_deleted[k].insert((depth,i));
                            
                            }
                        }
                    }                   
                }
                
                for (v,c) in outer_steps.iter(){
                    let commands = self.get_subproof_commands(v);
                    for (dd,y) in c.iter(){
                        let i = *y;
                        let d = *dd;
                        let clause = &commands[i];
                        match clause{
                            ProofCommand::Assume { id, term } => {
                                let mut current_parts: &mut PartTracker;
                                match referenced_by_parts.get_mut(&(depth,i)) {
                                    Some(value) => current_parts = value,
                                    None => {
                                        current_parts = &mut PartTracker::new();
                                        panic!("({d},{i}) is not referenced by any part");
                                    }
                                }
                                for (&k, &times) in &current_parts.data{
                                    if times>=2{
                                        part_units_queue[k].push((d,i));
                                        part_deleted[k].insert((d,i));
                                    }
                                    
                                    current_parts.inv_index.insert(k,parts[k].len());
                                    parts[k].push(ClauseData{
                                        index: Some((d,i)),
                                        data: ProofCommand::Assume{id: id.to_string(), term: term.clone()},
                                        local_premises: vec![]
                                    });
                                }
                                current_parts.register(0, parts[0].len());
                                parts[0].push(ClauseData{
                                    index: Some((depth,i)),
                                    data: ProofCommand::Assume{id: id.to_string(), term: term.clone()},
                                    local_premises: vec![]
                                });
                            }
                            ProofCommand::Step(ps) => {
                                if let Some(mut current_parts) = referenced_by_parts.get_mut(&(d,i)){
                                    for (&k, &times) in &current_parts.data{
                                        parts[k].push(ClauseData{
                                            index: Some((d,i)),
                                            data: ProofCommand::Step(ps.clone()),
                                            local_premises: vec![]
                                        });
                                        if coming_from_resolution.contains(&(d,i)){
                                            if times>=2 && ps.clause.len()==1{
                                                part_units_queue[k].push((d,i));
                                                part_deleted[k].insert((d,i));
                                            }
                                        }
                                    }
                                }
                            }
                            ProofCommand::Subproof(Sp) => {
                                let mut adrs_sp = adrs.clone();
                                adrs_sp.push(i);
                                compress_later.insert(adrs_sp);
                                let last_clause = self.subproof_conclusion(&Some(adrs.clone()));
                                let conclusion = &last_clause.clause;
                                let resumed_to_step = 
                                ProofStep {
                                    id: last_clause.id.clone(), 
                                    clause: conclusion.clone(), 
                                    rule: last_clause.rule.clone(), 
                                    premises: last_clause.premises.clone(), 
                                    args: last_clause.args.clone(), 
                                    discharge: last_clause.discharge.clone()
                                };

                                let mut current_parts: &mut PartTracker;
                                match referenced_by_parts.get_mut(&(d,i)) {
                                    Some(value) => current_parts = value,
                                    None => {
                                        current_parts = &mut PartTracker::new();
                                        panic!("({d},{i}) is not referenced by any part");
                                    }
                                }
                                for (&k, &times) in &current_parts.data{    
                                    parts[k].push(ClauseData{
                                        index: Some((d,i)),
                                        data: ProofCommand::Step(resumed_to_step.clone()),
                                        local_premises: vec![]
                                    });
                                
                                    if coming_from_resolution.contains(&(d,i)) && times>=2 && conclusion.len()==1{
                                        part_units_queue[k].push((d,i));
                                        part_deleted[k].insert((d,i));
                                    
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for v in compress_later{
            self.compress(&Some(v), outer_steps,_pool);
        }
        
        (parts, part_deleted, part_units_queue, referenced_by_parts)
    }



    // Iterates over parts that can be compressed
    // If some nodes of the proof were marked as deleted, recompute the clauses that used the deleted node as premise.
    // If a node has only one parent left, marks it as substituted by it's parent.
    // Also computes the index of the premises inside each part. This is done here just to avoid writing an additional loop. 

    // Return:
    // substituted_in_parts: A vector where the i-th element is a list of nodes in part i that were substituted by some parent 
    fn fix_broken_proof(
        &mut self,
        sub: &Option<Vec<usize>>,
        part_deleted: Vec<HashSet<(usize,usize)>>,
        parts: &mut Vec<Vec<ClauseData>>,
        depth: usize,
        proof_pool: &mut PrimitivePool 
    )->Result<Vec<HashMap<usize, usize>>,CompressionError>{
        let mut adrs = vec![];
        let mut commands;
        match sub{
            Some(addrs) => {
                adrs = addrs.clone();
                commands = self.get_subproof_commands(&adrs);
            }
            None => ()
        }
        let depth = adrs.len();
        let mut substituted_in_parts: Vec<HashMap<usize, usize>> = vec![HashMap::new();parts.len()];
        for current_part_id in 0..part_deleted.len(){
            parts[current_part_id].reverse();
            self.local_premises_computation(current_part_id, parts);
            if part_deleted[current_part_id].len()>0{
                for cl_data_ind in 0..parts[current_part_id].len(){
                    let current_clause = &parts[current_part_id][cl_data_ind];
                    //println!("fixing {cl_data_ind}");
                    match &current_clause.data{
                        ProofCommand::Assume {..} => (),
                        ProofCommand::Step(ps) => {
                            let args = ps.args.clone();
                            let mut not_missing_index: Vec<(usize, (usize, usize))> = Vec::new(); //(order of premise appearance, premise)
                            let aux = &current_clause.local_premises;
                            for j in 0..aux.len(){
                                let true_index: (usize, usize);
                                    match &parts[current_part_id][aux[j]].index{
                                        Some(k) => true_index = *k,
                                        None => panic!("Something went wrong with local_premises_computation")
                                    } 
                                
                                if !part_deleted[current_part_id].contains(&true_index){
                                    not_missing_index.push((j,aux[j]));
                                }
                            }
                            if not_missing_index.len()==1 && (&ps.rule=="resolution"||&ps.rule=="th-resolution"){
                                Self::substitute_node_by_parent(
                                    cl_data_ind,
                                    not_missing_index[0].1,
                                    &mut substituted_in_parts[current_part_id]
                                );
                            } else {
                                let current_index: (usize, usize);
                                match &parts[current_part_id][cl_data_ind].index{
                                    Some(indx ) => current_index = *indx,
                                    None => {
                                        current_index = (0,0);
                                        panic!("None index")
                                    }
                                }
                                if current_clause.local_premises.len()>0{
                                    let mut args_input: Option<Vec<ProofArg>> = None;
                                    let mut current_commands = commands;
                                    if (current_index.0!=depth){
                                        let slice = &adrs[0..(current_index.0+1)];
                                        current_commands = &self.get_subproof_commands(slice);
                                    }
                                    if let ProofCommand::Step(ps) = current_commands[current_index]{
                                        if not_missing_index.len()==ps.premises.len(){           //Heuristic, fix
                                            args_input = Some(args);
                                        } else {
                                            args_input = Self::select_args(&not_missing_index, &args);
                                        }
                                    } 
                                    self.generic_re_resolve_parted(
                                        current_part_id,
                                        cl_data_ind,
                                        &mut not_missing_index, 
                                        &mut substituted_in_parts,
                                        parts,
                                        args_input,
                                        Some(depth),
                                        proof_pool
                                    );
                                }
                            }
                        }
                        ProofCommand::Subproof(_) => ()//escrever para um exemplo do tipo let
                    }
                }
            }
        }        
        Ok(substituted_in_parts)
    }


/*
    // Insert the collected units and resolves them with the last element of each part and append them to the commands vector
    fn reinsert_units(
        &self,
        parts: &mut Vec<Vec<ClauseData>>, 
        part_units_queue: Vec<Vec<usize>>, 
        substituted_in_parts: &Vec<HashMap<usize, usize>>,
        referenced_by_parts: Vec<PartTracker>,
        proof_pool: &mut PrimitivePool
    )->()
    {
        for current_part in 0..parts.len(){
            if part_units_queue[current_part].len()>0{
                let part = &mut parts[current_part];
                let original_part_len = part.len();
                let mut current_root = part.len()-1;
                let substituted = &substituted_in_parts[current_part];
                if substituted.contains_key(&current_root){
                    current_root = *substituted.get(&current_root).unwrap();
                }
                let units_queue = &part_units_queue[current_part];
                //println!("Units queue of part {:?}: {:?}", current_part, units_queue);
                //println!("{:?} - units_queue: {:?}",current_part,units_queue);
                //println!("{:?} - substituted: {:?}",current_part,substituted);
                //println!("{:?} - refs:",current_part);
                /*for i in 0..referenced_by_parts.len(){
                    println!("{:?} - {:?}",i,&referenced_by_parts[i]);
                }*/
                
                for &u in units_queue{
                    //let mut args_op: Vec<ProofArg> = Vec::new();
                    let unit = u;
                    //println!("The unit is {:?}",unit);
                    let mut local_unit = self.general_to_local( 
                        unit, 
                        current_part, 
                        original_part_len, 
                        &referenced_by_parts);
                    //println!("Now the unit is mapped into {:?}",local_unit);
                    if substituted.contains_key(&local_unit){
                        local_unit = *substituted.get(&local_unit).unwrap();
                        //println!("Now the \"unit\" is substituted by {:?}",local_unit);
                    }
                    /*unit = part[local_unit].index as usize;
                    println!("Now the \"unit\" is remapped into {:?}",unit);
                    match &self.proof.commands[unit]{
                        ProofCommand::Assume { term,.. } => {
                            let removed_negations = term.remove_all_negations_with_polarity();
                            args_op.push(ProofArg::Term(removed_negations.1.clone()));
                            let parity = removed_negations.0;
                            args_op.push(ProofArg::Term(proof_pool.bool_constant(!parity)));
                        }
                        ProofCommand::Step(ps) => {
                            let terms = ps.clause.clone();
                            //let removed_negations = term.remove_all_negations_with_polarity();
                            //let parity = removed_negations.0;
                            //args_op.push(ProofArg::Term(removed_negations.1.clone()));
                            //args_op.push(ProofArg::Term(proof_pool.bool_constant(!parity)));
                        }
                        _ => ()
                    }*/
                    //println!("current root: {current_root}\nlocal unit: {local_unit}");
                    let args_op = self.args_new_clause(current_root, local_unit, part, proof_pool);
                    //println!("ARGS OPE: {:?}",&args_op);
                    let premises = Self::generic_build_premises_parted(part, vec![(0,current_root),(0,local_unit)],None);//Verificar, quebrado
                    //println!("PREMISES: {:?}",&premises);
                    let nc: Result<IndexSet<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<IndexSet<_>>(&premises, &args_op, proof_pool);
                    match nc{
                        Ok(c) => {
                            let new_clause_set: HashSet<Rc<Term>> = c.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                            let new_clause: Vec<Rc<Term>> = new_clause_set.into_iter().collect();
                            let new_proof_step = ProofStep{
                                id: "".to_string(),
                                clause: new_clause,
                                rule: "resolution".to_string(),
                                premises: vec![],
                                args: args_op,
                                discharge: vec![]
                            };
                            part.push(ClauseData{
                                index: -1,
                                data: ProofCommand::Step(new_proof_step),
                                local_premises: vec![current_root, local_unit]
                            });
                            current_root+=1;
                        },
                        Err(e) => {
                            println!("checker error");
                            println!("Premises {:?}",&premises);
                            println!("Arguments {:?}",&args_op);
                            println!("{:?}",e)
                        }
                    }
                    
                }
            }
        }
    }


    // Creates a new proof. The nodes collected by the collect_units are used only at the end of each part and the nodes
    // substituted by fix_broken_proof are ignored. This ensures the final proof will be valid and the parts altered by this 
    // process will be smaller than they were in the original proof.
    fn rebuild(
        &mut self, 
        substituted_in_parts: Vec<HashMap<usize,usize>>, 
        parts: Vec<Vec<ClauseData>>,
        sub: Option<SubExpanded>
    ) -> () {
        let mut a = "".to_owned();
        let mut t = "".to_owned();
        let mut d = 0;
        let mut commands = &self.proof.commands;
        match &sub{
            None => {
                a = "a".to_owned();
                t = "t".to_owned();
            }
            Some(v) => {
                commands = self.get_subproof_commands(v);
                let mut q = 0;
                /*{
                    let mut com = &self.proof.commands;
                    let mut aux: &ProofCommand;
                    for j in 0..v.len()-1{   //dive into layers of commands to fetch the commands of the subproof being traversed
                        let i = v[j];
                        aux = &com[i];
                        match aux{
                            ProofCommand::Subproof(spp) => com = &spp.commands,
                            _ => panic!("Error in addressing subproofs") //Add error
                        }
                        q = j+1;
                    }
                    let i = v[q];
                    if let ProofCommand::Subproof(to_check) = &com[i]{
                        println!("{:?}",to_check);
                    }

                }*/


                d = v.len();
                if let ProofCommand::Subproof(sp) = &self.proof.commands[v[0]]{
                    let sub_len = sp.commands.len();
                    if let ProofCommand::Step(ps) = &sp.commands[sub_len-1]{
                        a = ps.id.clone();
                    }
                }
                for i in &v[1..]{
                    if let ProofCommand::Subproof(sp) = &self.proof.commands[*i]{
                        let sub_len = sp.commands.len();
                        if let ProofCommand::Step(ps) = &sp.commands[sub_len-1]{
                            a = format!("{}.{}",a,ps.id.clone());
                        }
                    }
                }
                t = format!("{}.t",a);
                a = format!("{}.a",a);
            }            
        }
        let mut new_commands: Vec<ProofCommand> = vec![];
        let mut assume_ind: usize = 0;
        let mut step_ind: usize = 0;
        let mut _subproof_ind: usize = 0;
        let mut found_assertions: HashMap<Rc<Term>,usize> = HashMap::new();
        let mut found_clauses: HashMap<Vec<Rc<Term>>,usize> = HashMap::new();
        let a_slc = &a[..];
        let t_slc = &t[..];
        for assum in &parts[0]{
            if let ProofCommand::Assume{term,..} = &assum.data{
                if !found_assertions.contains_key(term){
                    new_commands.push(ProofCommand::Assume{id: format!("{}{}",a_slc,assume_ind), term: term.clone()});
                    assume_ind += 1;
                    found_assertions.insert(term.clone(),new_commands.len()-1);
                }
            }
        }
        for part_ind in (2..parts.len()).rev(){
            let substituted = &substituted_in_parts[part_ind];
            let part = &parts[part_ind];
            for local_ind in 0..parts[part_ind].len(){
                //println!("Here {:?}",&part[local_ind].data);
                match &part[local_ind].data{
                    ProofCommand::Assume { term,.. } =>{
                        if !found_assertions.contains_key(&term){
                            new_commands.push(ProofCommand::Assume{id: format!("{}{}",a_slc,assume_ind), term: term.clone()});
                            assume_ind += 1;
                            found_assertions.insert(term.clone(),new_commands.len()-1);
                        }
                    }
                    ProofCommand::Step(ps) => {
                        if !found_clauses.contains_key(&ps.clause) && !substituted.contains_key(&local_ind){
                            let mut formated_prem: Vec<(usize,usize)> = vec![];
                            if &part[local_ind].local_premises.len()>&0{
                                for &premm in &part[local_ind].local_premises{
                                    let mut prem = premm;
                                    if substituted.contains_key(&prem){
                                        prem = *substituted.get(&prem).unwrap();
                                    }
                                    match &part[prem].data{
                                        ProofCommand::Assume{term,..} => {
                                            formated_prem.push((d, *found_assertions.get(term).unwrap()));
                                        }
                                        ProofCommand::Step(pps) => {
                                            formated_prem.push((d, *found_clauses.get(&pps.clause.clone()).unwrap()));
                                        }
                                        ProofCommand::Subproof(_) => ()
                                    }
                                }
                            } else {
                                //construct a vector analogue to the local premises in the block above referencing premises outside of the part
                                if let ProofCommand::Step(pps) = &commands[part[local_ind].index as usize]{
                                    let analogue = &pps.premises;
                                    for &(dpt, prem) in analogue{
                                        match &commands[prem]{
                                            ProofCommand::Assume{term,..} =>
                                                formated_prem.push((d, *found_assertions.get(term).unwrap())),
                                            ProofCommand::Step(p3s) => {
                                                formated_prem.push((d, *found_clauses.get(&p3s.clause.clone()).unwrap()));}
                                            ProofCommand::Subproof(_) => ()
                                        }
                                    }
                                }
                            }
                            let formated_step: ProofStep = ProofStep{
                                clause: ps.clause.clone(),
                                id: format!("{}{}",t_slc,step_ind),
                                premises: formated_prem,
                                rule: ps.rule.clone(),
                                args: ps.args.clone(),
                                discharge: vec![]
                            };
                            found_clauses.insert(formated_step.clause.clone(), new_commands.len());
                            new_commands.push(ProofCommand::Step(formated_step));
                            step_ind += 1;
                        }
                    }
                    ProofCommand::Subproof(sp) => {//possible bug
                        ()
                    }
                }
            }
        }
        let part = &parts[1];
        for local_ind in 0..parts[1].len(){
            match &part[local_ind].data{
                ProofCommand::Step(ps) => {
                    if !found_clauses.contains_key(&ps.clause){
                        let mut formated_prem: Vec<(usize,usize)> = vec![];
                        if &part[local_ind].local_premises.len()>&0{
                            for &prem in &part[local_ind].local_premises{
                                match &part[prem].data{
                                    ProofCommand::Assume{term,..} => {
                                        formated_prem.push((d, *found_assertions.get(term).unwrap()));
                                    }
                                    ProofCommand::Step(pps) => {
                                        formated_prem.push((d, *found_clauses.get(&pps.clause.clone()).unwrap()));
                                    }
                                    ProofCommand::Subproof(_) => ()
                                }
                            }
                        } else {
                            //construct a vector analogue to the local premises in the block above referencing premises outside of the part
                            if let ProofCommand::Step(pps) = &commands[part[local_ind].index as usize]{
                                let analogue = &pps.premises;
                                for &(_, prem) in analogue{
                                    match &commands[prem]{
                                        ProofCommand::Assume{term,..} =>
                                            formated_prem.push((d, *found_assertions.get(term).unwrap())),
                                        ProofCommand::Step(p3s) => {
                                            formated_prem.push((d, *found_clauses.get(&p3s.clause.clone()).unwrap()));}
                                        ProofCommand::Subproof(_) => ()
                                    }
                                }
                            }
                        }
                        let mut subproof_ending = false;
                        if let ProofCommand::Step(ending) = &part[local_ind].data {
                            if self.sp_binder.contains(&ending.rule[..]){
                                subproof_ending = true;
                            }
                        }
                        let formated_step;
                        if subproof_ending{
                            let slc_len = t_slc.len();
                            let outer_id =  &t_slc.to_string()[..slc_len-2];
                            formated_step = ProofStep{
                                clause: ps.clause.clone(),
                                id: format!("{}",outer_id),
                                premises: formated_prem,
                                rule: ps.rule.clone(),
                                args: ps.args.clone(),
                                discharge: ps.discharge.clone()
                            };
                        }else{
                            formated_step = ProofStep{
                                clause: ps.clause.clone(),
                                id: format!("{}{}",t_slc,step_ind),
                                premises: formated_prem,
                                rule: ps.rule.clone(),
                                args: ps.args.clone(),
                                discharge: vec![]
                            };
                        }
                        
                        found_clauses.insert(formated_step.clause.clone(), new_commands.len());
                        new_commands.push(ProofCommand::Step(formated_step));
                        step_ind += 1;
                    }
                }
                _ => ()
            }
        }
        let mut commands = &mut self.proof.commands;
        match &sub{
            None => self.proof.commands = new_commands,
            Some(sp) => {
                commands = self.get_mut_subproof_commands(sp);
                *commands = new_commands;
            }
        }
    
    }
*/

    // Assigns indices of the elements of the ind-th part that points to the location within the part of the premises of each clause
    fn local_premises_computation(
        &self,
        ind: usize,
        parts: &mut Vec<Vec<ClauseData>>
    )->(){
        let part = &parts[ind];
        //map from the global index of a clause to the local index of every clause that uses it as a premise 
        //the first element of the pair is the order in which the premise is used by the clause
        let mut table_prem: HashMap<(usize, usize), Vec<(usize, (usize, usize))>> = HashMap::new();

        //map from global index to local index
        let mut table_pos: HashMap<(usize, usize), usize> = HashMap::new();
        
        let mut prem_length: Vec<usize> = vec![];
        for i in 0..part.len(){  
            let key: (usize, usize);
            match &part[i].index{
                Some(k) => key = *k,
                None => panic!("Wrong call of local_premises_computation")
            } 
            table_pos.insert(key, i);
            match &part[i].data{
                ProofCommand::Step(ps) => {
                    let mut j = 0;
                    for dp in &ps.premises{
                        table_prem.entry(*dp).or_insert_with(Vec::new).push((j,key));
                        j+=1;
                    }
                    if ps.rule=="or" && self.proof.commands[ps.premises[0].1].is_assume(){
                        prem_length.push(0);
                    }else{
                        let mut aux: usize = 0;
                        for dp in &ps.premises{
                            if table_pos.contains_key(dp){
                                aux+=1;
                            }
                        }
                        prem_length.push(aux);
                    }
                }
                _  => prem_length.push(0),
            }
        }
        let mut_part = &mut parts[ind];
        for i in 0..mut_part.len(){
            mut_part[i].local_premises = vec![0;prem_length[i]];
        }
        for i in 0..mut_part.len(){
            let key: (usize, usize);
            match &part[i].index{
                Some(k) => key = *k,
                None => panic!("Wrong call of local_premises_computation")
            } 
            if table_prem.contains_key(&key){
                for &(ord,pr) in table_prem.get(&key).unwrap(){
                    let loc_prem = &mut mut_part[*table_pos.get(&pr).unwrap()].local_premises;
                    loc_prem[ord] = i;
                }
            }
        }     
        
    }

/*
    // Receives a part, an index and a vector containing a tuple representing the premises of the ind-th clause of the part that are not
    // marked for deletion. The 1st element of the tuple is the order of the premise in the vector of premises of the clause
    // and the 2nd element in the tuple is the index of the premise within the part.

    // Return:
    // Option of a vector with arguments used to recompute a resolution in the case that some of it's premises were marked for deletion.
    pub fn generic_get_args_parted(
        part: &Vec<ClauseData>, 
        ind: usize, 
        not_missing: &Vec<(usize,usize)>
    ) -> Option<Vec<ProofArg>>{
        if let ProofCommand::Step(ps) = &part[ind].data{
            //println!("ind: {:?}",ind);
            //println!("not_missing: {:?}", &not_missing);
            let mut arg_vec: Vec<ProofArg> = Vec::new();
            let premise_number = &ps.args.len()/2;
            let remaining_indexes: Vec<usize> = not_missing.iter().map(|(i,_)| *i).collect();
            let remaining_set: HashSet<usize> = remaining_indexes.clone().into_iter().collect();
            let range_set: HashSet<usize> = (0..premise_number).collect();
            let missing_set: HashSet<usize> = range_set.difference(&remaining_set).cloned().collect();
            let mut flag_start: usize = 1;
            if !missing_set.contains(&0) && !missing_set.contains(&1){
                arg_vec.push(ps.args[0].clone());
                arg_vec.push(ps.args[1].clone());
                flag_start = 2;
            }
            for i in flag_start..remaining_indexes.len(){
                if !missing_set.contains(&remaining_indexes[i]){
                    arg_vec.push(ps.args[2*remaining_indexes[i]-2].clone());
                    arg_vec.push(ps.args[2*remaining_indexes[i]-1].clone());
                }
            }
            return Some(arg_vec)
        } else {
            return None
        }
    }

*/
    fn generic_re_resolve_parted(
        &mut self, 
        part_ind: usize, 
        cl_data_ind: usize,
        not_missing: &mut Vec<(usize,usize)>,
        substituted_parts: &mut Vec<HashMap<usize,usize>>,
        parts: &mut Vec<Vec<ClauseData>>,
        args_op: Option<Vec<ProofArg>>, 
        depth: Option<usize>,
        proof_pool: &mut PrimitivePool
    ) -> (){
        
        let part = &mut parts[part_ind];
        let substituted = &mut substituted_parts[part_ind];
        match &mut part[cl_data_ind].data{
            ProofCommand::Step(_) =>{
                for i in 0..not_missing.len(){
                    if substituted.contains_key(&not_missing[i].1){
                        not_missing[i].1 = *substituted.get(&not_missing[i].1).unwrap();
                    } 
                }
                /*if cl_data_ind==17{
                    println!("Not missing: {:?}", &not_missing);
                }*/
                match args_op{
                    Some(argss)=>{
                        let mut d = 0;
                        match &depth{
                            Some(dpt) => d = *dpt,
                            None => ()
                        }
                        let mut args = argss;
                        let mut premises = Self::generic_build_premises_parted(part, not_missing.clone(),depth);
                        //println!("inner premises: {:?}", &premises);
                        /*println!("Premises: {:?}",&premises);
                        println!("Args: {:?}", &args);
                        println!("nm {:?}", &not_missing);
                        */
                        let resolution: Result<IndexSet<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution::<IndexSet<_>>(&premises, &args, proof_pool);
                        match resolution{
                            Ok(r) => {
                                /*if cl_data_ind==17{
                                    println!("R {:?}",&r);
                                }*/   
                                let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                                /*if cl_data_ind==17{
                                    println!("Resolvent set {:?}",&resolvent_set);
                                } */      
                                let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                                /*if cl_data_ind==17{
                                    println!("Resolvent {:?}",&resolvent);
                                } */
                                part[cl_data_ind].local_premises = not_missing.iter().map(|(_,s)| *s).collect();
                                let mut new_premises: Vec<(usize,usize)> = vec![];
                                for &k in &part[cl_data_ind].local_premises{
                                    let j = part[k].index as usize;
                                    new_premises.push((d,j));
                                } 
                                if let ProofCommand::Step(pps) = &mut part[cl_data_ind].data{
                                    //println!("Changing");
                                    pps.args = args;
                                    pps.clause = resolvent;
                                    pps.premises = new_premises;
                                    //println!("Updated {:?}: {:?}",cl_data_ind,pps);
                                }
                            },
                            _ => {
                                println!("Error: Clauses couldn't be resolved");
                                println!("Resolving for {:?} on part {:?}", cl_data_ind, part_ind);
                                println!("Premises: {:?}", premises);
                                println!("Arguments: {:?}", args)
                            }
                        }
                    }
                    None => println!("Error: arguments couldn't be found")
                }
            }
            _ => ()
        }
    }


    fn generic_build_premises_parted(part: &Vec<ClauseData>, not_missing: Vec<(usize,usize)>, depth: Option<usize>)->Vec<Premise> {
        let mut ans: Vec<Premise> = vec![];
        let mut d = 0;
        match depth{
            Some(dpt) => d = dpt,
            None => ()
        } 
        for i in not_missing{
            ans.push(Premise::new((d,i.1),&part[i.1].data));
        }
        ans
    }
/*
    fn args_new_clause(&self, id_left: usize, id_right:usize, part: &Vec<ClauseData>, proof_pool: &mut PrimitivePool) -> Vec<ProofArg>{
        let term_r = match &part[id_right].data{
            ProofCommand::Assume{term,..} => vec![term.clone()],
            ProofCommand::Step(ps) => ps.clause.clone(),
            ProofCommand::Subproof(_) => vec![]
        };
        let term_l = match &part[id_left].data{
            ProofCommand::Assume{term,..} => vec![term.clone()],
            ProofCommand::Step(ps) => ps.clause.clone(),
            ProofCommand::Subproof(_) => vec![]
        };
        //println!("term r: {:?}\nterm l: {:?}",&term_r,&term_l);
        let term_r_polar_set: HashSet<_> = term_r.iter().map(|x| x.remove_all_negations_with_polarity()).collect();
        let term_l_polar_set: HashSet<_> = term_l.iter().map(|x| x.remove_all_negations_with_polarity()).collect();
        let term_r_set: HashSet<_> = term_r_polar_set.iter().map(|(_, x)| x.clone()).collect();
        let term_l_set: HashSet<_> = term_l_polar_set.iter().map(|(_, x)| x.clone()).collect();
        let intersection: Vec<_> = term_r_set.intersection(&term_l_set).collect();
        //println!("Set r: {:?}\nSet l: {:?}",&term_r_set,&term_l_set);
        //println!("Inter: {:?}",&intersection);
        for candidate in intersection{
            let arg_term = candidate.clone();
            if term_r_polar_set.contains(&(true,arg_term)) && term_l_polar_set.contains(&(false,arg_term)){
                let args_op: Vec<ProofArg> = vec![ProofArg::Term(arg_term.clone()),ProofArg::Term(proof_pool.bool_constant(false))];
                return args_op;
            } else if term_r_polar_set.contains(&(false,arg_term)) && term_l_polar_set.contains(&(true,arg_term)){
                let args_op: Vec<ProofArg> = vec![ProofArg::Term(arg_term.clone()),ProofArg::Term(proof_pool.bool_constant(true))];
                return args_op;
            }
        }
        vec![]
    }

    fn mirror_inverse_index(ind: usize, length: usize)->usize{
        length-ind-1
    }*/
    
    fn get_subproof_commands(&self, sp: &[usize]) -> &Vec<ProofCommand>{
        let mut commands = &self.proof.commands;
        let mut aux: &ProofCommand;
        for &i in sp{   //dive into layers of commands to fetch the commands of the subproof being traversed
            aux = &commands[i];
            match aux{
                ProofCommand::Subproof(spp) => commands = &spp.commands,
                _ => panic!("Error in addressing subproofs") //Add error
            }
        }
        commands
    }
/*
    fn get_mut_subproof_commands(&mut self, sp: &Vec<usize>) -> &mut Vec<ProofCommand>{
        let mut commands = &mut self.proof.commands;
        let mut aux: &mut ProofCommand;
        for &i in sp{   //dive into layers of commands to fetch the commands of the subproof being traversed
            aux = &mut commands[i];
            match aux{
                ProofCommand::Subproof(spp) => commands = &mut spp.commands,
                _ => panic!("Error in addressing subproofs") //Add error
            }
        }
        commands
    }

    pub fn print(&self, sub: &Option<Vec<usize>>)->(){
        let mut ind = 0;
        let mut commands = &self.proof.commands;
        match sub{
            None => (),
            Some(sp) => commands = self.get_subproof_commands(sp)
        }
        for i in &self.proof.commands{
            match i{
                ProofCommand::Assume { id, term } => println!("{:?} - Assume {:?}: {:?}",ind,id,term),
                ProofCommand::Step(ps) => println!("{:?} - Step {:?}: prem: {:?}; clause: {:?}; rule: {:?}",ind,ps.id,ps.premises,ps.clause,ps.rule),
                ProofCommand::Subproof(sp)=> {
                    println!("{ind} - Subproof:");
                    print_subproof(&sp,Some(1));
                }
            }
            ind+=1;
        }
    }

    #[warn(dead_code)]
    pub fn inspect_subproof(&self, i:usize) -> (){
        let mut ind: usize = 0;
        for j in self.proof.commands.iter(){
            if let ProofCommand::Subproof(sp) = j{
                if ind==i{
                    print_subproof(&sp,Some(1));
                } else {
                    ind+=1;
                }
            }
        }
    }

    fn general_to_local(&self, 
        ind:usize, 
        part_id: usize, 
        part_len: usize, 
        referenced_by_parts: &Vec<PartTracker>
    ) -> usize{
        let mut ind = *referenced_by_parts[ind].inv_index.get(&part_id).unwrap();
        ind = Self::mirror_inverse_index(ind, part_len);
        ind
    }
    */
    fn subproof_conclusion(&self, adrs: &Option<Vec<usize>>)-> &ProofStep{
        match adrs{
            Some(ad) =>
            {
                let commands = self.get_subproof_commands(ad);
                let last_command = &commands[commands.len()-1];
                match last_command{
                    ProofCommand::Assume { id, term } => panic!("You subproof {:?} ends with an assume?\nSomething might be wrong here",ad),
                    ProofCommand::Step(ps) => &ps,
                    ProofCommand::Subproof(sp) => panic!("You subproof {:?} ends with another subproof?\nSomething might be wrong here",ad)
                }
            }
            None => panic!("No subproof address given")
        }
    }

    fn empty_premises(commands: &Vec<ProofCommand>, i: usize) -> bool{
        match &commands[i]{
            ProofCommand::Assume {..} => false,
            ProofCommand::Step(ps) => ps.premises.len()==0,
            ProofCommand::Subproof(sp) => Self::empty_premises(&sp.commands,sp.commands.len()-1)
        }
    }

    fn collecting_resolutions(&self, 
        depth: usize, i: usize,
        sub: &Option<Vec<usize>>, 
        referenced_by_parts: &mut HashMap<(usize, usize), PartTracker>, 
        coming_from_resolution: &mut HashSet<(usize,usize)>,
        part_units_queue: &mut Vec<Vec<(usize,usize)>>,
        part_deleted: &mut Vec<HashSet<(usize,usize)>>,
        parts: &mut Vec<Vec<ClauseData>>,
        outer_steps: &mut IndexMap<Vec<usize>,IndexSet<(usize,usize)>>,
        ps: &ProofStep
    ) -> (){
        let mut adrs = vec![];
        match sub{
            Some(addrs) => {
                adrs = addrs.clone();
            }
            None => ()
        }
        /*let mut current_parts: &mut PartTracker;
        match referenced_by_parts.get_mut(&(depth,i)) {
            Some(value) => current_parts = value,
            None => {
                current_parts = &mut PartTracker::new();
                panic!("({depth},{i}) is not referenced by any part");
            }
        }*/
        let mut part_references: Vec<(usize,usize,usize)> = vec![];
        if let Some(mut current_parts) = referenced_by_parts.get_mut(&(depth,i)){
            let mut new_tracker = PartTracker::new();
            if !coming_from_resolution.contains(&(depth,i)){ 
                let new_part = parts.len();
                part_units_queue.push(Vec::new());
                part_deleted.push(HashSet::new());
                current_parts = &mut new_tracker;
                parts.push(Vec::new());
                current_parts.insert(new_part);
            }

            for (&k, &times) in &current_parts.data{
                //Counts how many times each premise shows up in the current parts 
                for &(d, j) in &ps.premises{
                    //must anotate instead of updating references due to borrow checker
                    part_references.push((d,j,k));
                    coming_from_resolution.insert((d,j));

                    //anotate each step from distinct command vectors
                    if d!=depth{
                        let higher_adrs = adrs[0..d+1].to_vec();
                        outer_steps.entry(higher_adrs)
                        .and_modify(|c| {c.insert((d,j));}).
                        or_insert(IndexSet::from([(d,j)]));
                    }
                }
                
                
                //add the current clause to it's parts
                parts[k].push(ClauseData{
                    index: Some((depth,i)),
                    data: ProofCommand::Step(ps.clone()),
                    local_premises: vec![]
                });

                //checks if the current clause must be collected
                if times>=2 && ps.clause.len()==1{
                    part_units_queue[k].push((depth,i));
                    part_deleted[k].insert((depth,i));
                }
            }
        }
        for (d,j,k) in part_references{
            referenced_by_parts.entry((d,j)).or_insert_with(|| PartTracker::new()).insert(k);
            //Anotate the position of the current clause in each of the current parts
            if let Some(mut current_parts) = referenced_by_parts.get_mut(&(depth,i)){
                current_parts.register(k,parts[k].len());
            }
        }

    }

    fn collecting_resolution_premises(&self, 
        depth: usize, i: usize,
        sub: &Option<Vec<usize>>, 
        referenced_by_parts: &mut HashMap<(usize, usize), PartTracker>, 
        coming_from_resolution: &mut HashSet<(usize,usize)>,
        part_units_queue: &mut Vec<Vec<(usize,usize)>>,
        part_deleted: &mut Vec<HashSet<(usize,usize)>>,
        parts: &mut Vec<Vec<ClauseData>>,
        outer_steps: &mut IndexMap<Vec<usize>,IndexSet<(usize,usize)>>,
        ps: &ProofStep
    ) -> (){
        let mut adrs = vec![];
        match sub{
            Some(addrs) => {
                adrs = addrs.clone();
            }
            None => ()
        }
        let (premise_depth, premise_loc) = ps.premises[0];
        let premise: &ProofCommand;
        if premise_depth==depth{
            premise = &self.proof.commands[premise_loc];
        } else {
            let slice = &adrs[0..(premise_depth+1)];
            premise = &self.get_subproof_commands(slice)[premise_loc];
        }

        if ps.rule=="or" && premise.is_assume(){ //if the rule is an "or" applied over an "assume", anotate the assume only in the part 0
            referenced_by_parts.entry((premise_depth, premise_loc)).or_insert_with(|| PartTracker::new()).insert(0);
        } else {
        //create a new part for each premise of the node, as each premise may
        //come from an independent resolution tree
            for &(d, j) in &ps.premises{
                let new_part = parts.len();
                part_units_queue.push(Vec::new());
                part_deleted.push(HashSet::new());
                referenced_by_parts.entry((d, j)).or_insert_with(|| PartTracker::new()).insert(new_part);
                parts.push(Vec::new());

                //anotate each step from distinct command vectors
                if d!=depth{
                    let higher_adrs = adrs[0..d+1].to_vec();
                        outer_steps.entry(higher_adrs)
                        .and_modify(|c| {c.insert((d,j));}).
                        or_insert(IndexSet::from([(d,j)]));
                }
            }

            let mut current_parts: &mut PartTracker;
            match referenced_by_parts.get_mut(&(depth,i)) {
                Some(value) => current_parts = value,
                None => {
                    current_parts = &mut PartTracker::new();
                    panic!("({depth},{i}) is not referenced by any part");
                }
            }

            //add the current clause to it's parts
            for (&k, &times) in &current_parts.data{
                parts[k].push(ClauseData{
                    index: Some((depth,i)),
                    data: ProofCommand::Step(ps.clone()),
                    local_premises: vec![]
                });

                //checks if the current clause must be collected
                if times>=2 && ps.clause.len()==1{
                    part_units_queue[k].push((depth,i));
                    part_deleted[k].insert((depth,i));
                }
            }
        }
    }

    fn not_resoltion_nor_premises(&self, 
        depth: usize, i: usize,
        referenced_by_parts: &mut HashMap<(usize, usize), PartTracker>, 
        parts: &mut Vec<Vec<ClauseData>>,
        ps: &ProofStep
    ) -> (){
        let mut to_collect: Vec<((usize,usize),usize)> = vec![];
        if let Some(ref mut current_parts) = referenced_by_parts.get(&(depth,i)){
            for (&k, &times) in &current_parts.data{
                for &(d ,j) in &ps.premises{
                    to_collect.push(((d,j),k));
                }
                
                parts[k].push(ClauseData{
                    index: Some((depth,i)),
                    data: ProofCommand::Step(ps.clone()),
                    local_premises: vec![]
                });
            }
        } else {
            panic!("({depth},{i}) is not referenced by any part");
        }
        for ((d,j),k) in to_collect{
            referenced_by_parts.entry((d, j)).or_insert_with(|| PartTracker::new()).insert(k);
        }
    }

}