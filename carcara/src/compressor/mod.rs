//Task: write general version of lower units in Latex using an abstraction level of the same level as the original article.
//Important: Never modify a proof more than needed

//OPT: Implement reinsert_units_parted with at maximum one resolution for each part
//OPT: The PartTracker vectors can use less space if split in two variables
//OPT: write lifetime anotations to make found_clauses use references as keys in rebuild_parted
//WARN: assume after steps

use crate::ast::*;
use std::collections::{HashSet, HashMap};
use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
use indexmap::IndexSet;
use std::env;
mod error;
use crate::compressor::error::{CompressionError, CollectionError};

#[derive(Debug)]
pub struct ProofCompressor{
    proof: Proof,
}

#[derive(Debug)]
pub struct ClauseData{
    index: i32,
    data: ProofCommand,
    local_premises: Vec<usize>
}


#[derive(Debug, Clone, Default)]
pub struct PartTracker{
    data: HashMap<usize,usize>,
    inv_index: HashMap<usize, usize>
}

impl PartTracker{
    fn new()->PartTracker{
        PartTracker{
            data: HashMap::new(),
            inv_index: HashMap::new()
        }
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

pub fn print_part_ids(part: &Vec<ClauseData>, part_n: Option<usize>)->(){
    match part_n{
        Some(j) => println!("Parte {j}"),
        None => ()
    }
    for i in 0..part.len(){
        match &part[i].data{
            ProofCommand::Assume { id,.. } => println!("{:?} - {:?}",i,id),
            ProofCommand::Step(ps) => {
                println!("{:?} - {:?}", i, &ps.id);
            },
            _ => ()
        }
    }
}


impl ProofCompressor{
    pub fn new(p: &Proof)->ProofCompressor{
        ProofCompressor{
            proof: p.clone()
        }
    }

    pub fn print_part_ids_prems(&self, part: &Vec<ClauseData>, part_n: Option<usize>)->(){
        match part_n{
            Some(j) => println!("Parte {j}"),
            None => ()
        }
        for i in 0..part.len(){
            match &part[i].data{
                ProofCommand::Assume { id,.. } => println!("{:?} - {:?}",i,id),
                ProofCommand::Step(ps) => {
                    let mut prem: Vec<String> = vec![];
                    for &(_,p) in &ps.premises{
                        match &self.proof.commands[p]{
                            ProofCommand::Assume {id, term} => prem.push(id.clone()),
                            ProofCommand::Step(pps) => prem.push(pps.id.clone()),
                            _ => ()
                        }
                    }
                    let indexes: Vec<_> = ps.premises.iter().map(|(_,x)| *x).collect();
                    println!("{:?}/{:?} - {:?}, premises: {:?}, indexes: {:?}", i, &part[i].index, &ps.id, prem, indexes);
                },
                _ => ()
            }
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
        match self.compress(_pool){
            Err(e) => {
                match e{
                    CompressionError::Collection(_) => println!("There is no collectable clauses."),
                    CompressionError::SubproofNotImplementedYet => (),//println!("The logic to compress subproofs is yet to be implemented."),
                    CompressionError::ResolutionError(res) => println!("There was an error when resolving the clauses {:?}.",res),
                }
            }
            Ok(()) => ()
        }
        self.get_proof()
    }

    pub fn get_proof(&self) -> Proof{
        return self.proof.clone()
    }

    pub fn compress(&mut self, _pool: &mut PrimitivePool) -> Result<(),CompressionError>{
        //self.print();
        match self.collect_units(){
            Err(e) => return Err(CompressionError::Collection(e)),
            Ok((mut parts,
                part_deleted,
                part_units_queue,
                referenced_by_parts)) => {
                //println!("queues: {:?}",&part_units_queue);
                let substituted_in_parts = self.fix_broken_proof(
                    part_deleted,
                    &mut parts,
                    _pool
                )?;
                self.reinsert_units(&mut parts, part_units_queue, &substituted_in_parts, referenced_by_parts, _pool);
                
                self.rebuild(substituted_in_parts,parts);
            }
        };
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

    // referenced_by_parts: Vector of PartTrackers, position i stores all parts that contain the node i and how many times
    // this node is used inside that part
    pub fn collect_units(&self)->
        Result<(Vec<Vec<ClauseData>>,
        Vec<HashSet<usize>>,
        Vec<Vec<usize>>,
        Vec<PartTracker>), CollectionError>
    {
        //self.print();
        let n = self.proof.commands.len();
        let mut parts: Vec<Vec<ClauseData>> = vec![Vec::new(),Vec::new()];
        let mut referenced_by_parts: Vec<PartTracker> = vec![PartTracker::new();n];
        referenced_by_parts[n-1].insert(1);
        let mut part_units_queue: Vec<Vec<usize>> = vec![Vec::new(),Vec::new()];
        let mut part_deleted: Vec<HashSet<usize>> = vec![HashSet::new(),HashSet::new()];
        let mut coming_from_resolution: Vec<bool> = vec![false;n];
        for i in (0..self.proof.commands.len()).rev(){
            let pc = &self.proof.commands[i];
            match pc{
                ProofCommand::Assume{id, term} => {
                    let current_part = referenced_by_parts[i].clone();
                    for (k, times) in current_part.data{
                        if times>=2{
                            part_units_queue[k].push(i);
                            part_deleted[k].insert(i);
                        }
                        referenced_by_parts[i].register(k, parts[k].len());
                        parts[k].push(ClauseData{
                            index: i as i32,
                            data: ProofCommand::Assume{id: id.to_string(), term: term.clone()},
                            local_premises: vec![]
                        });
                    }                     
                }
                ProofCommand::Step(ps) => {
                    let is_resolution = ps.rule=="resolution"||ps.rule=="th-resolution";
                    if is_resolution{
                        let current_part = referenced_by_parts[i].clone();
                        for (k, times) in &current_part.data{
                            for (_, j) in &ps.premises{
                                referenced_by_parts[*j].insert(*k);
                                coming_from_resolution[*j] = true;
                            }
                            referenced_by_parts[i].register(*k,parts[*k].len());
                            parts[*k].push(ClauseData{
                                index: i as i32,
                                data: ProofCommand::Step(ps.clone()),
                                local_premises: vec![]
                            });
                            if *times>=2 && ps.clause.len()==1{
                                part_units_queue[*k].push(i);
                                part_deleted[*k].insert(i);
                            }
                        }
                    } else {
                        if coming_from_resolution[i] == true{
                            
                            if ps.rule=="or" && self.proof.commands[ps.premises[0].1].is_assume(){
                                referenced_by_parts[ps.premises[0].1].insert(0);
                                let current_part = &referenced_by_parts[i];
                                for (k, _) in &current_part.data{
                                    parts[*k].push(ClauseData{
                                        index: i as i32,
                                        data: ProofCommand::Step(ps.clone()),
                                        local_premises: vec![]
                                    });
                                }                                
                            } else {
                                for (_, j) in &ps.premises{
                                    let new_part = parts.len();
                                    part_units_queue.push(Vec::new());
                                    part_deleted.push(HashSet::new());
                                    referenced_by_parts[*j].insert(new_part);
                                    parts.push(Vec::new());
                                }
                                let current_part = &referenced_by_parts[i];
                                for (k, _) in &current_part.data{
                                    parts[*k].push(ClauseData{
                                        index: i as i32,
                                        data: ProofCommand::Step(ps.clone()),
                                        local_premises: vec![]
                                    });
                                }
                            }
                        } else {
                            let current_part = &referenced_by_parts[i].clone();
                            for (k, _) in &current_part.data{
                                for (_,j) in &ps.premises{
                                    referenced_by_parts[*j].insert(*k);
                                }
                                parts[*k].push(ClauseData{
                                    index: i as i32,
                                    data: ProofCommand::Step(ps.clone()),
                                    local_premises: vec![]
                                });
                            }
                        }
                    }
                    //println!("Referenced by parts[{:?}]: {:?}", i, &referenced_by_parts[i]);
                }
                ProofCommand::Subproof(_) => (),
            }
        }
        let mut compressible_parts: usize = 0;
        for p in &part_deleted{
            if p.len()>0{
                compressible_parts+=1;
            }
        }
        
        if compressible_parts==0{
            return Err(CollectionError);
        }
        /*for i in 0..parts.len(){
            print_part(&parts[i], Some(i));
        }*/
        Ok((parts, part_deleted, part_units_queue, referenced_by_parts))
    }



    // Iterates over parts that can be compressed
    // If some nodes of the proof were marked as deleted, recompute the clauses that used the deleted node as premise.
    // If a node has only one parent left, marks it as substituted by it's parent.
    // Also computes the index of the premises inside each part. This is done here just to avoid writing an additional loop. 

    // Return:
    // substituted_in_parts: A vector where the i-th element is a list of nodes in part i that were substituted by some parent 
    fn fix_broken_proof(
        &mut self,
        part_deleted: Vec<HashSet<usize>>,
        parts: &mut Vec<Vec<ClauseData>>,
        proof_pool: &mut PrimitivePool 
    )->Result<Vec<HashMap<usize, usize>>,CompressionError>{
        
        let mut substituted_in_parts: Vec<HashMap<usize, usize>> = vec![HashMap::new();parts.len()];
        for current_part_id in 0..part_deleted.len(){
            parts[current_part_id].reverse();
            //self.print_part_ids_prems(&parts[current_part_id], Some(current_part_id));
            //println!("");
            self.local_premises_computation(current_part_id, parts);
            /*if current_part_id==1{
                print_part(&parts[current_part_id],Some(current_part_id));
            }*/
            if part_deleted[current_part_id].len()>0{
                for cl_data_ind in 0..parts[current_part_id].len(){
                    let current_clause = &parts[current_part_id][cl_data_ind];
                    //println!("fixing {cl_data_ind}");
                    match &current_clause.data{
                        ProofCommand::Assume {..} => (),
                        ProofCommand::Step(ps) => {
                            let args = ps.args.clone();
                            let mut not_missing_index: Vec<(usize, usize)> = Vec::new();
                            let aux = &current_clause.local_premises;
                            for j in 0..aux.len(){
                                let true_index = &(parts[current_part_id][aux[j]].index as usize);
                                if !part_deleted[current_part_id].contains(true_index){
                                    not_missing_index.push((j,aux[j]));
                                }
                            }
                            /*if cl_data_ind==5{
                                println!("{:?}",ps);
                                println!("Not missing: {:?}",&not_missing_index);
                                println!("Args: {:?}",&args);
                            }*/
                            if not_missing_index.len()==1 && (&ps.rule=="resolution"||&ps.rule=="th-resolution"){
                                Self::substitute_node_by_parent(
                                    cl_data_ind,
                                    not_missing_index[0].1,
                                    &mut substituted_in_parts[current_part_id]
                                );
                            } else {
                                let current_index = parts[current_part_id][cl_data_ind].index as usize;
                                if current_clause.local_premises.len()>0{
                                    let mut args_input: Option<Vec<ProofArg>> = None;
                                    if let ProofCommand::Step(ps) = &self.proof.commands[current_index]{
                                        if not_missing_index.len()==ps.premises.len(){           //Heuristic, fix
                                            args_input = Some(args);
                                        } else {
                                            args_input = Self::select_args(&not_missing_index, &args);
                                        }
                                    } 
                                    /*if current_part_id==1{
                                        println!("Re-resolving {cl_data_ind}");
                                    }
                                    if cl_data_ind==17{
                                        println!("Subs: {:?}", &substituted_in_parts[current_part_id]);
                                        println!("Args: {:?}",&args_input);
                                    }*/
                                    self.generic_re_resolve_parted(
                                        current_part_id,
                                        cl_data_ind,
                                        &mut not_missing_index, 
                                        &mut substituted_in_parts,
                                        parts,
                                        args_input,
                                        proof_pool
                                    );
                                    /*if let ProofCommand::Step(ps) =  &parts[current_part_id][cl_data_ind].data{
                                        println!("Clause: {:?}",ps.clause.clone());
                                    }*/
                                }
                            }
                        }
                        ProofCommand::Subproof(_) => ()
                    }
                }
            }
        }
        Ok(substituted_in_parts)
    }



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
                //println!("{:?} - units_queue: {:?}",current_part,units_queue);
                //println!("{:?} - substituted: {:?}",current_part,substituted);
                //println!("{:?} - refs:",current_part);
                /*for i in 0..referenced_by_parts.len(){
                    println!("{:?} - {:?}",i,&referenced_by_parts[i]);
                }*/
                
                for &u in units_queue{
                    let mut args_op: Vec<ProofArg> = Vec::new();
                    let mut unit = u;
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
                    let premises = Self::generic_build_premises_parted(part, vec![(0,current_root),(0,local_unit)]);
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
        parts: Vec<Vec<ClauseData>>
    ) -> () {
        let mut new_commands: Vec<ProofCommand> = vec![];
        let mut assume_ind: usize = 0;
        let mut step_ind: usize = 0;
        let mut _subproof_ind: usize = 0;
        let mut found_assertions: HashMap<Rc<Term>,usize> = HashMap::new();
        let mut found_clauses: HashMap<Vec<Rc<Term>>,usize> = HashMap::new();
        for assum in &parts[0]{
            if let ProofCommand::Assume{term,..} = &assum.data{
                if !found_assertions.contains_key(term){
                    new_commands.push(ProofCommand::Assume{id: format!("a{assume_ind}"), term: term.clone()});
                    assume_ind += 1;
                    found_assertions.insert(term.clone(),new_commands.len()-1);
                }
            }
        }
        for part_ind in (1..parts.len()).rev(){
            let substituted = &substituted_in_parts[part_ind];
            let part = &parts[part_ind];
            for local_ind in 0..parts[part_ind].len(){
                //println!("Here {:?}",&part[local_ind].data);
                match &part[local_ind].data{
                    ProofCommand::Assume { term,.. } =>{
                        if !found_assertions.contains_key(&term){
                            new_commands.push(ProofCommand::Assume{id: format!("a{assume_ind}"), term: term.clone()});
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
                                            formated_prem.push((0, *found_assertions.get(term).unwrap()));
                                        }
                                        ProofCommand::Step(pps) => {
                                            formated_prem.push((0, *found_clauses.get(&pps.clause.clone()).unwrap()));
                                        }
                                        ProofCommand::Subproof(_) => ()
                                    }
                                }
                            } else {
                                //construct a vector analogue to the local premises in the block above referencing premises outside of the part
                                if let ProofCommand::Step(pps) = &self.proof.commands[part[local_ind].index as usize]{
                                    let analogue = &pps.premises;
                                    for &(_, prem) in analogue{
                                        match &self.proof.commands[prem]{
                                            ProofCommand::Assume{term,..} =>
                                                formated_prem.push((0, *found_assertions.get(term).unwrap())),
                                            ProofCommand::Step(p3s) => {
                                                formated_prem.push((0, *found_clauses.get(&p3s.clause.clone()).unwrap()));}
                                            ProofCommand::Subproof(_) => ()
                                        }
                                    }
                                }
                            }
                            let formated_step: ProofStep = ProofStep{
                                clause: ps.clause.clone(),
                                id: format!("t{step_ind}"),
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
                    ProofCommand::Subproof(sp) => {
                        new_commands.push(ProofCommand::Subproof(sp.clone()));
                        _subproof_ind += 1;
                    }
                }
            }
        }
        self.proof.commands = new_commands;
    }


    // Assigns indices of the elements of the ind-th part that points to the location within the part of the premises of each clause
    fn local_premises_computation(
        &self,
        ind: usize,
        parts: &mut Vec<Vec<ClauseData>>
    )->(){
        let part = &parts[ind];
        //map from the global index of a clause to the local index of every clause that uses it as a premise 
        //the first element of the pair is the order in which the premise is used by the clause
        let mut table_prem: HashMap<usize, Vec<(usize,usize)>> = HashMap::new();

        //map from global index to local index
        let mut table_pos: HashMap<usize, usize> = HashMap::new();
        
        let mut prem_length: Vec<usize> = vec![];
        for i in 0..part.len(){   
            let key = part[i].index as usize;
            table_pos.insert(key, i);    
            /*if ind==2 && i==4{
                println!("match:\n{:?}",&part[i].data);
            }*/
            match &part[i].data{
                ProofCommand::Step(ps) => {
                    let mut j = 0;
                    for (_,p) in &ps.premises{
                        table_prem.entry(*p).or_insert_with(Vec::new).push((j,key));
                        j+=1;
                    }
                    /*if ind==2 && i==4{
                        println!("indo pro if ps.rule!=\"or\"");
                        println!("{:?}",&ps.rule);
                    }*/
                    if ps.rule=="or" && self.proof.commands[ps.premises[0].1].is_assume(){
                        prem_length.push(0);
                    }else{
                           /*if ind==2 && i==4{
                            println!("o problemático entrou no if ps.rule!=\"or\"");
                            println!("table_pos: {:?}",&table_pos);
                            println!("premises: {:?}",&ps.premises);
                        }*/
                        let mut aux: usize = 0;
                        for (_, p) in &ps.premises{
                            if table_pos.contains_key(p){
                                aux+=1;
                            }
                        }
                        prem_length.push(aux);
                    }
                }
                _  => prem_length.push(0),
            }
        }
        /*if ind==2{
            //print_part(&parts[2], Some(2));
            println!("local premises space: {:?}", &prem_length);
            println!("table of premises:\n{:?}",&table_prem);
            println!("table of positions:\n{:?}",&table_pos);
            //println!("{:?}",prem_length.len());
            //println!("{:?}",prem_length[4]);
            //prem_length[4] = 1; 
        }*/
        let mut_part = &mut parts[ind];
        for i in 0..mut_part.len(){
            mut_part[i].local_premises = vec![0;prem_length[i]];
        }
        for i in 0..mut_part.len(){
            let key = mut_part[i].index as usize;
            
            if table_prem.contains_key(&key){
                for &(ord,pr) in table_prem.get(&key).unwrap(){
                    let loc_prem = &mut mut_part[*table_pos.get(&pr).unwrap()].local_premises;
                    loc_prem[ord] = i;
                }
            }
        }     
        
    }


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


    fn generic_re_resolve_parted(
        &mut self, 
        part_ind: usize, 
        cl_data_ind: usize,
        not_missing: &mut Vec<(usize,usize)>,
        substituted_parts: &mut Vec<HashMap<usize,usize>>,
        parts: &mut Vec<Vec<ClauseData>>,
        args_op: Option<Vec<ProofArg>>, 
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
                        let mut args = argss;
                        let mut premises = Self::generic_build_premises_parted(part, not_missing.clone());
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
                                    new_premises.push((0,j));
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


    fn generic_build_premises_parted(part: &Vec<ClauseData>, not_missing: Vec<(usize,usize)>)->Vec<Premise> {
        let mut ans: Vec<Premise> = vec![];
        for i in not_missing{
            ans.push(Premise::new((0,i.1),&part[i.1].data));
        }
        ans
    }

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
    }
    
    pub fn print(&self)->(){
        let mut ind = 0;
        for i in &self.proof.commands{
            match i{
                ProofCommand::Assume{id,term} => println!("{ind} - Assume {:?}: {:?}",id,term),
                ProofCommand::Step(ps) => println!("{ind} - {:?} {:?}: {:?}->{:?}",ps.rule,ps.id,ps.premises,ps.clause),
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
}