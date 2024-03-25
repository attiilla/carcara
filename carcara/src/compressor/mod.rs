//use ahash::{AHashMap, AHashSet};
//use indexmap::IndexMap;
//use indexmap::IndexSet;
use crate::ast::*;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;
//use std::thread::current;
use multiset::HashMultiSet;
use crate::checker::rules::Premise;
//use crate::checker::rules::RuleArgs;
use crate::checker::rules::resolution::{apply_generic_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
//use std::time::Duration;
//use std::sync::Arc;
use std::env;

mod error;
use crate::compressor::error::{CompressionError, CollectionError};

//cvc5 file --dump-proof --proof-format-mode=alethe --proof-granularity=theory-rewrite
//ignorar passos de subproof

#[derive(Debug)]
pub struct ProofCompressor<'a>{
    pub _original_proof: &'a Proof,
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
    data: HashMap<usize,usize>
}

impl PartTracker{
    fn new()->PartTracker{
        PartTracker{
            data: HashMap::new(),
        }
    }

    fn insert(&mut self, a: usize) -> (){
        if self.data.contains_key(&a){
            *self.data.entry(a).or_insert(0) += 1;
        } else {
            self.data.insert(a,1);
        }
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


impl<'a> ProofCompressor<'a>{
    pub fn new(p: &Proof)->ProofCompressor{
        ProofCompressor{
            _original_proof: &p,
            proof: p.clone()
        }
    }

    fn substitute_node_by_parent(
        &self,
        ind: usize,
        unitary_parent_ind: usize,
        substituted: &mut HashMap<usize,usize>
    ) -> (){
        if let ProofCommand::Step(node) = &self.proof.commands[ind]{
            let mut substitute = node.premises[unitary_parent_ind].1;
            if substituted.contains_key(&substitute){
                substitute = *substituted.get(&substitute).unwrap();
            }
            substituted.insert(ind, substitute);
        }
    }

    fn substitute_node_by_parent_old(//working fine if the proof has only resolutions and or rules
        &self,
        ind: usize,
        unitary_parent_ind: usize,
        substituted: &mut HashMap<usize,usize>
    ) -> (){
        if let ProofCommand::Step(node) = &self.proof.commands[ind]{
            let mut substitute = node.premises[unitary_parent_ind].1;
            if substituted.contains_key(&substitute){
                substitute = *substituted.get(&substitute).unwrap();
            }
            substituted.insert(ind, substitute);
        }
    }


    pub fn run_compressor(&'a mut self, _pool: &mut PrimitivePool) -> (){
        env::set_var("RUST_BACKTRACE", "1");
        match self.compress(_pool){
            Err(e) => {
                println!("Error");
                match e{
                    CompressionError::Collection(_) => println!("There is no collectable clauses."),
                    CompressionError::SubproofNotImplementedYet => println!("The logic to compress subproofs is yet to be implemented."),
                    CompressionError::ResolutionError(res) => println!("There was an error when resolving the clauses {:?}.",res),
                }
            }
            Ok(()) => ()
        }
        ()
    }

    pub fn compress(&'a mut self, _pool: &mut PrimitivePool) -> Result<(),CompressionError>{
        env::set_var("RUST_BACKTRACE", "1");
        match self.collect_units(){
            Err(e) => return Err(CompressionError::Collection(e)),
            Ok((units_queue, del)) => {
                let substituted = self.fix_broken_proof(del,_pool)?;
                self.handled_reinsert_units(units_queue, &substituted, _pool)?;
                self.rebuild(&substituted);
                let _ = print_proof(&self.proof.commands, true);
            }
        };
        Ok(())
    }

    pub fn compress_parted(&'a mut self, _pool: &mut PrimitivePool) -> Result<(),CompressionError>{
        match self.collect_units_parted(){
            Err(e) => return Err(CompressionError::Collection(e)),
            Ok((mut parts,
                part_deleted,
                part_units_queue,
                referenced_by_parts)) => {
                let substituted_in_parts = self.fix_broken_proof_parted(
                    part_deleted,
                    &mut parts,
                    _pool
                )?;
                self.reinsert_units_parted(&mut parts, part_units_queue, substituted_in_parts, _pool);
                //self.handled_reinsert_units(units_queue, &substituted, _pool)?;
                //self.rebuild(&substituted);
                let _ = print_proof(&self.proof.commands, true);
            }
        };
        Ok(())
    }

    fn collect_units(&self)->Result<(Vec<usize>, HashSet<usize>),CollectionError>{
        let mut units_queue: Vec<usize> = vec![]; 
        let mut deleted: HashSet<usize> = HashSet::new();  
        let mut resolution_premises: HashMultiSet<usize> = HashMultiSet::new();

        for i in (0..self.proof.commands.len()).rev(){
            let pc = &self.proof.commands[i];
            match pc{
                ProofCommand::Assume{..} => {
                    if resolution_premises.count_of(&i)>=2{
                        units_queue.push(i);
                        deleted.insert(i);
                    }
                }
                ProofCommand::Step(ps) => {
                    let is_resolution = ps.rule=="resolution";
                    if is_resolution{
                        for (_,j) in ps.premises.clone(){
                            resolution_premises.insert(j);
                        }
                        if resolution_premises.count_of(&i)>=2 && ps.clause.len()==1{
                            units_queue.push(i);
                            deleted.insert(i);
                        }
                    }
                }
                ProofCommand::Subproof(_) => ()
            }
        }
        if units_queue.len()>0{
            return Ok((units_queue, deleted));
        }
        return Err(CollectionError);
    }

    pub fn collect_units_parted(&self)->
        Result<(Vec<Vec<ClauseData>>,
        Vec<HashSet<usize>>,
        Vec<Vec<usize>>,
        Vec<PartTracker>), CollectionError>
    {
        self.print();
        let n = self.proof.commands.len();
        //let mut current_part: HashMultiSet<usize> = HashMultiSet::new();
        let mut parts: Vec<Vec<ClauseData>> = vec![Vec::new()];
        //parts[0].push(length-1);
        
        //position i stores all parts that contain the current node i and how many times this node is used inside that part
        let mut referenced_by_parts: Vec<PartTracker> = vec![PartTracker::new();n];
        referenced_by_parts[n-1].insert(0);
        let mut part_units_queue: Vec<Vec<usize>> = vec![Vec::new()];
        let mut part_deleted: Vec<HashSet<usize>> = vec![HashSet::new()];
        let mut coming_from_resolution: Vec<bool> = vec![false;n];
        
        for i in (0..self.proof.commands.len()).rev(){
            let pc = &self.proof.commands[i];
            
            match pc{
                ProofCommand::Assume{id, term} => {
                    let current_part = &referenced_by_parts[i];
                    for (k, times) in &current_part.data{
                        if *times>=2{
                            part_units_queue[*k].push(i);
                            part_deleted[*k].insert(i);
                        }
                        if coming_from_resolution[i] == true{
                            parts[*k].push(ClauseData{
                                index: i as i32,
                                data: ProofCommand::Assume{id: id.to_string(), term: term.clone()},
                                local_premises: vec![]
                            });
                        }
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
                            let new_part = parts.len();
                            part_units_queue.push(Vec::new());
                            part_deleted.push(HashSet::new());
                            for (_, j) in &ps.premises{
                                referenced_by_parts[*j].insert(new_part);
                            }
                            parts.push(Vec::new());
                            let current_part = &referenced_by_parts[i];
                            for (k, _) in &current_part.data{
                                parts[*k].push(ClauseData{
                                    index: i as i32,
                                    data: ProofCommand::Step(ps.clone()),
                                    local_premises: vec![]
                                });
                            }
                            /*parts[new_part].push(ClauseData{
                                index: i,
                                data: ProofCommand::Step(ps.clone())
                            })*/;
                        } else {
                            let current_part = &referenced_by_parts[i];
                            for (k, _) in &current_part.data{
                                parts[*k].push(ClauseData{
                                    index: i as i32,
                                    data: ProofCommand::Step(ps.clone()),
                                    local_premises: vec![]
                                });
                            }
                        }
                    }
                }
                ProofCommand::Subproof(_) => (),
            }
            
        }
        //if units_queue.len()>0{
        //    return Ok((units_queue, deleted));
        //}
        //return Err(CollectionError);
        /*println!("Parts:");
        for v in 0..parts.len(){
            println!("{:?}:",v);
            for i in 0..parts[v].len(){
                println!("{:?}-{:?}: {:?}", v, i, &parts[v][i])
            }
        }
        println!("Parts units queue: {:?}", &part_units_queue);
        println!("Parts deleted: {:?}",&part_deleted);
        println!("Coming from resolution: {:?}",&coming_from_resolution);
        println!("Referenced by parts: {:?}",&referenced_by_parts);*/
        Ok((parts, part_deleted, part_units_queue, referenced_by_parts))
    }

    fn fix_broken_proof_parted(
        &mut self,
        part_deleted: Vec<HashSet<usize>>,
        parts: &mut Vec<Vec<ClauseData>>,
        proof_pool: &mut PrimitivePool 
    )->Result<Vec<HashMap<usize, usize>>,CompressionError>{
        let mut substituted_in_parts: Vec<HashMap<usize, usize>> = vec![HashMap::new();parts.len()];
        for current_part_id in 0..part_deleted.len(){
            if part_deleted[current_part_id].len()>0{
                /*println!("Part being fixed: {current_part_id}");*/
                for i in 0..parts[current_part_id].len(){
                    println!("{:?}-{:?}: {:?}", current_part_id, i, &parts[current_part_id][i])
                }
                /*println!("parts[{:?}].len() = {:?}",current_part_id,parts[current_part_id].len());
                println!("Iterator: {:?}", (0..parts[current_part_id].len()+1).rev());*/
                let n: usize = parts[current_part_id].len();
                for cl_data_ind in (0..n).rev() {
                    //let cl_data_ind = 0;
                    let true_index = parts[current_part_id][cl_data_ind].index as usize;
                    //println!("{:?}-{:?}: {:?}", current_part_id, cl_data_ind, &parts[current_part_id][cl_data_ind]);
                    match &self.proof.commands[true_index]{
                        ProofCommand::Assume {..} => (),
                        ProofCommand::Step(ps) => {
                            let mut not_missing_index: Vec<(usize, usize)> = Vec::new();
                            let aux = &ps.premises.clone();
                            for j in 0..aux.len(){
                                if !part_deleted[current_part_id].contains(&aux[j].1){
                                    not_missing_index.push((j,aux[j].1.clone()));
                                }
                            }
                            if not_missing_index.len()==1 && (&ps.rule=="resolution"||&ps.rule=="th-resolution"){
                                self.substitute_node_by_parent(true_index, not_missing_index[0].0, &mut substituted_in_parts[current_part_id]);
                            } else {
                                if not_missing_index.len()!=ps.premises.len() || not_missing_index.iter().any(|(_,key)| substituted_in_parts[current_part_id].contains_key(key)){
                                    /*println!("Substituted: ");
                                    //for z in 0..substituted_in_parts.len(){
                                    let z = 1;
                                    println!("{:?} - {:?}",z,&substituted_in_parts[z]);
                                    //}*/
                                    self.generic_re_resolve_parted(true_index,
                                        current_part_id,
                                        cl_data_ind,
                                        &mut not_missing_index, 
                                        &mut substituted_in_parts,
                                        parts,
                                        proof_pool);
                                }
                            }
                        }
                        ProofCommand::Subproof(_) => ()
                    }
                }
            }
        }
        /*println!("Parts:");
        for v in 0..parts.len(){
            println!("{:?}:",v);
            for i in 0..parts[v].len(){
                println!("{:?}-{:?}: {:?}", v, i, &parts[v][i])
            }
        }
        println!("substituted at end:");
        for k in 0..substituted_in_parts.len(){
            println!("{:?} - {:?}",k,&substituted_in_parts[k]);
        }*/
        Ok(substituted_in_parts)
    }
    
    fn fix_broken_proof(
        &mut self,
        deleted: HashSet<usize>,
        proof_pool: &mut PrimitivePool 
    )->Result<HashMap<usize, usize>,CompressionError>{
        self.print();
        let mut substituted: HashMap<usize, usize> = HashMap::new();
        for i in 0..self.proof.commands.len(){
            match &self.proof.commands[i]{
                ProofCommand::Assume {..} => (),
                ProofCommand::Step(ps) => {
                    if ps.rule=="th-resolution"||ps.rule=="resolution"{
                        let mut not_missing_index: Vec<(usize, usize)> = Vec::new();
                        let aux = ps.premises.clone();
                        for j in 0..aux.len(){
                            if !deleted.contains(&aux[j].1){
                                not_missing_index.push((j,aux[j].1.clone()));
                            }
                        }
                        if not_missing_index.len()==1{
                            self.substitute_node_by_parent(i, not_missing_index[0].0, &mut substituted);
                        } else {
                            if not_missing_index.len()!=ps.premises.len() || not_missing_index.iter().any(|(_,key)| substituted.contains_key(key)){
                                self.generic_re_resolve(i, &mut not_missing_index, &substituted, proof_pool);
                            }
                        }
                    }
                }
                ProofCommand::Subproof(_) => ()
            }
        }
        self.print();
        Ok(substituted)
        
    }


    fn reinsert_units_parted(
        &mut self,
        parts: &mut Vec<Vec<ClauseData>>,
        part_units_queue: Vec<Vec<usize>>,
        substituted_in_parts: Vec<HashMap<usize, usize>>,
        proof_pool: &mut PrimitivePool
    )->()
    {
        
        for i in 0..parts.len(){
            self.local_premises_computation(i, parts);
            //self.part_reinsertion(i, parts, &part_units_queue, &substituted_in_parts, proof_pool)
        }
    }

    fn local_premises_computation(
        &self,
        ind: usize,
        parts: &mut Vec<Vec<ClauseData>>
    )->(){
        let part = &parts[ind];
        let mut table_prem: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut table_pos: HashMap<usize, usize> = HashMap::new();
        for i in 0..part.len(){
            let key = part[i].index as usize;
            table_pos.insert(key, i);
            
            match &part[i].data{
                ProofCommand::Step(ps) => {
                    for (_,p) in &ps.premises{
                        table_prem.entry(*p).or_insert_with(Vec::new).push(key);
                    }
                }
                _  => ()
            }
        }
        let mut mut_part = &mut parts[ind];
        for i in 0..mut_part.len(){
            let key = mut_part[i].index as usize;
            if table_prem.contains_key(&key){
                for &pr in table_prem.get(&key).unwrap(){
                    let mut loc_prem = &mut mut_part[*table_pos.get(&pr).unwrap()].local_premises;
                    loc_prem.push(i)
                }
            }
        }
        if ind==1{
            println!("Table_premises:");
            println!("{:?}",&table_prem);
            println!("Table_pos:");
            println!("{:?}",&table_pos);
            println!("\n\nLocal premises computation {ind}");
            for i in 0..mut_part.len(){
                println!("{:?}-{:?}: {:?}",ind , i, &mut_part[i])
            }
        }
        
    }

    fn part_reinsertion(
        &self,
        ind: usize,
        parts: &mut Vec<Vec<ClauseData>>, 
        part_units_queue: &Vec<Vec<usize>>, 
        substituted_in_parts: &Vec<HashMap<usize, usize>>,
        proof_pool: &mut PrimitivePool
    )->()
    {
        let mut part = &mut parts[ind];
        let mut current_root = part[0].index as usize;
        part.reverse();
        let units_queue = &part_units_queue[ind];
        let substituted = &substituted_in_parts[ind];
        

        for &u in units_queue{
            let mut args_op: Vec<ProofArg> = Vec::new();
            match &self.proof.commands[u]{
                ProofCommand::Assume { id, term } => {
                    let removed_negations = term.remove_all_negations_with_polarity();
                    args_op.push(ProofArg::Term(removed_negations.1.clone()));
                    let parity = removed_negations.0;
                    args_op.push(ProofArg::Term(proof_pool.bool_constant(!parity)));
                }
                ProofCommand::Step(ps) => {
                    let term = ps.clause[0].clone();
                    let removed_negations = term.remove_all_negations_with_polarity();
                    let parity = removed_negations.0;
                    args_op.push(ProofArg::Term(removed_negations.1.clone()));
                    args_op.push(ProofArg::Term(proof_pool.bool_constant(!parity)));
                }
                _ => ()
            }
            let mut unit = u;
            if substituted.contains_key(&unit){
                unit = *substituted.get(&unit).unwrap();
            }
            if args_op.len()!=0{
                let premises = Self::build_premises(&self.proof.commands, current_root, unit);
                //println!("args_op: {:?},\npremises: {:?}",&args_op,&premises);
                let nc: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args_op, proof_pool);
                match nc{
                    Ok(c) => {
                        let new_clause_set: HashSet<Rc<Term>> = c.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                        let new_clause: Vec<Rc<Term>> = new_clause_set.into_iter().collect();
                        let new_proof_step = ProofStep{
                            id: "".to_string(),
                            clause: new_clause,
                            rule: "resolution".to_string(),
                            premises: vec![(0,current_root),(0,unit)],
                            args: args_op,
                            discharge: vec![]
                        };
                        part.push(ClauseData{
                            index: -1,
                            data: ProofCommand::Step(new_proof_step),
                            local_premises: vec![]
                        });
                        current_root+=1;
                    },
                    Err(_e) => ()
                }
            }
        }

    }

    fn handled_reinsert_units(
        &mut self,
        units_queue: Vec<usize>,
        substituted: &HashMap<usize,usize>,
        proof_pool: &mut PrimitivePool
    )->Result<(),CompressionError> {
        let mut current_root = self.proof.commands.len()-1;
        for u in units_queue{
            let mut args_op: Vec<ProofArg> = Vec::new();
            //let mut subproof_flag = false;
            match self.proof.commands[u].clone(){
                ProofCommand::Assume { id, term } => {
                    let removed_negations = term.remove_all_negations_with_polarity();
                    args_op.push(ProofArg::Term(removed_negations.1.clone()));
                    let parity = removed_negations.0;
                    args_op.push(ProofArg::Term(proof_pool.bool_constant(!parity)));
                }
                ProofCommand::Step(ps) => {
                    let term = ps.clause[0].clone();
                    let removed_negations = term.remove_all_negations_with_polarity();
                    let parity = removed_negations.0;
                    args_op.push(ProofArg::Term(removed_negations.1.clone()));
                    args_op.push(ProofArg::Term(proof_pool.bool_constant(!parity)));
                }
                _ => ()
            }
            let mut unit = u;
            if substituted.contains_key(&unit){
                unit = *substituted.get(&unit).unwrap();
            }
            if args_op.len()!=0{
                let premises = Self::build_premises(&self.proof.commands, current_root, unit);
                //println!("args_op: {:?},\npremises: {:?}",&args_op,&premises);
                let nc: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args_op, proof_pool);
                match nc{
                    Ok(c) => {
                        let new_clause_set: HashSet<Rc<Term>> = c.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                        let new_clause: Vec<Rc<Term>> = new_clause_set.into_iter().collect();
                        let new_proof_step = ProofStep{
                            id: "".to_string(),
                            clause: new_clause,
                            rule: "resolution".to_string(),
                            premises: vec![(0,current_root),(0,unit)],
                            args: args_op,
                            discharge: vec![]
                        };
                        self.proof.commands.push(ProofCommand::Step(new_proof_step));
                        current_root+=1;
                    },
                    Err(_e) => {
                       let res = vec![(0,current_root),(0,unit)];
                        return Err(CompressionError::ResolutionError(res));
                    }
                }
            }
        }
        return Ok(());
    }


    fn rebuild(&mut self, substituted: &HashMap<usize,usize>) -> (){
        let mut assume_ind: usize = 0;
        let mut step_ind: usize = 0;
        let mut _subproof_ind: usize = 0;
        let mut new_commands: Vec<ProofCommand> = vec![];
        let mut new_index_table: HashMap<usize,usize> = HashMap::new();
        for index in 0..self.proof.commands.len(){
            if !substituted.contains_key(&index){
                match &mut self.proof.commands[index]{
                    ProofCommand::Assume{term,..} => {
                        new_commands.push(ProofCommand::Assume{id: format!("a{assume_ind}"), term: term.clone()});
                        assume_ind += 1;
                    }
                    ProofCommand::Step(ps) => {
                        ps.id = format!("t{step_ind}");
                        for (_depth, p) in ps.premises.iter_mut() {
                            if substituted.contains_key(p){
                                *p = *substituted.get(p).unwrap();
                            }
                            if new_index_table.contains_key(p){
                                *p = *new_index_table.get(p).unwrap();
                            }
                        }
                        new_commands.push(ProofCommand::Step(ps.clone()));
                        step_ind += 1;
                    }
                    ProofCommand::Subproof(sp) => {
                        new_commands.push(ProofCommand::Subproof(sp.clone()));
                        _subproof_ind += 1;
                    }
                }
                new_index_table.insert(index,new_commands.len()-1);
            }
        }
        self.proof.commands = new_commands;
    }

    /*pub fn print(&self)->(){
        for i in &self.proof.commands{
            match i{
                ProofCommand::Assume{id,term} => println!("Assume {:?}: {:?}",id,term),
                ProofCommand::Step(ps) => println!("Resolution {:?}: {:?}->{:?}",ps.id,ps.premises,ps.clause),
                _ => ()
            }
        }
    }*/
    fn extract_term(&self, p: &ProofCommand) -> Vec<Rc<Term>>{
        let terms: Vec<Rc<Term>>;
        terms = match p{
            ProofCommand::Assume {term,.. } => vec![term.clone()],
            ProofCommand::Step(ps) => ps.clause.clone(),
            ProofCommand::Subproof(sp) => {
                match sp.commands.iter().last(){
                    Some(pc) => self.extract_term(pc),
                    None => panic!("Empty subproof")
                }
            }
        };
        terms
    }

    pub fn find_args(&self,i: usize, j: usize, proof_pool: &mut PrimitivePool) -> Option<Vec<ProofArg>>{
        fn compare_possible_pivot(p: (u32, &Rc<Term>), q: (u32, &Rc<Term>)) -> bool{
            // check if the literals are distinct && compares how many not they have to see if they can  be used as pivot
            if (p.1==q.1)&&(p.0%2!=q.0%2){
                return true;
            }
            false
        }
        let terms_left: &Vec<Rc<Term>> = &self.extract_term(&self.proof.commands[i]);
        let terms_right: &Vec<Rc<Term>> = &self.extract_term(&self.proof.commands[j]);
        let non_negated_terms_left: Vec<(u32, &Rc<Term>)> = terms_left.iter().map(|term| term.remove_all_negations()).collect();
        let non_negated_terms_right: Vec<(u32, &Rc<Term>)> = terms_right.iter().map(|term| term.remove_all_negations()).collect();
        let aux_set: HashSet<(u32, &Rc<Term>)> = non_negated_terms_left.clone().into_iter().collect();
        let pp = non_negated_terms_right.into_iter().find(|&x| 
                                                    aux_set.iter().any(|&y| 
                                                            compare_possible_pivot(x,y)));
        match pp{
            Some(parity_pivot) => {
                let order_arg: bool = parity_pivot.0%2!=0;
                let pivot = parity_pivot.1.clone();
                let args = vec![ProofArg::Term(pivot), ProofArg::Term(proof_pool.bool_constant(order_arg))];
                return Some(args)
            }
            None => return None
        }
    }

    pub fn generic_get_args(&self, ind: usize, not_missing: &Vec<(usize,usize)>, proof_pool: &mut PrimitivePool) -> Option<Vec<ProofArg>>{
        /*println!("ind: {:?}\nnot_missing: {:?}",ind,&not_missing);
        println!("Command: {:?}",&self.proof.commands[ind]);
        println!("Command1: {:?}",&self.proof.commands[not_missing[0].1]);
        println!("Command2: {:?}",&self.proof.commands[not_missing[1].1]);*/
        if let ProofCommand::Step(ps) = &self.proof.commands[ind]{
            let mut arg_vec: Vec<ProofArg> = Vec::new();
            //println!("Args: {:?}",&ps.args);
            //println!("Non missing: {:?}",&not_missing);
            let premise_number = &ps.args.len()/2;
            let remaining_indexes: Vec<usize> = not_missing.iter().map(|(i,_)| *i).collect();
            let remaining_set: HashSet<usize> = remaining_indexes.clone().into_iter().collect();
            let range_set: HashSet<usize> = (0..premise_number).collect();
            let missing_set: HashSet<usize> = range_set.difference(&remaining_set).cloned().collect();
            //let missing_indexes: Vec<usize> = missing_set.into_iter().collect();
            let mut flag_start: usize = 1;
            //println!("checkpoint0");
            //println!("args {:?}",ps.args);
            if !missing_set.contains(&0) && !missing_set.contains(&1){
                arg_vec.push(ps.args[0].clone());
                arg_vec.push(ps.args[1].clone());
                //println!("entrou");
                flag_start = 2;
            }
            /*println!("Remaining: {:?}", &remaining_indexes);
            println!("Missing: {:?}", &missing_set);
            println!("checkpoint1");
            println!("{:?}",flag_start..remaining_indexes.len());*/
            for i in flag_start..remaining_indexes.len(){
                //println!("checkpoint {:?}",i+2);
                if !missing_set.contains(&remaining_indexes[i]){
                //println!("Args to get: {:?}, {:?}", 2*remaining_indexes[i]-2, 2*remaining_indexes[i]-1);
                    arg_vec.push(ps.args[2*remaining_indexes[i]-2].clone());
                    arg_vec.push(ps.args[2*remaining_indexes[i]-1].clone());
                }
            }
            //println!("Returning {:?}", &arg_vec);
            return Some(arg_vec)
        } else {
            return None
        }
    }

    fn re_resolve(
        &mut self, 
        ind: usize, 
        substituted: &HashMap<usize,usize>, 
        proof_pool: &mut PrimitivePool
    ) -> (){
        match self.proof.commands[ind].clone(){
            ProofCommand::Step(ps) =>{
                let mut left_ind = ps.premises[0].1;
                let mut right_ind = ps.premises[1].1;
                if substituted.contains_key(&left_ind){
                    left_ind = *substituted.get(&left_ind).unwrap();
                }
                if substituted.contains_key(&right_ind){
                    right_ind = *substituted.get(&right_ind).unwrap();
                }
                println!("Resolving {:?} and {:?}", left_ind, right_ind);
                let args_op = self.find_args(left_ind,right_ind, proof_pool);
                match args_op{
                    Some(args)=>{
                        let premises = Self::build_premises(&self.proof.commands, left_ind, right_ind);
                        let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args, proof_pool);
                        match resolution{
                            Ok(r) => {
                                let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                                let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                                if let ProofCommand::Step(pps) = &mut self.proof.commands[ind]{
                                    pps.args = args;
                                    pps.clause = resolvent;
                                }
                            },
                            _ => println!("Error: Clauses couldn't be resolved")
                        }
                    }
                    None => println!("Error: arguments couldn't be found")
                }
            }
            _ => ()
        }
    }

    fn generic_re_resolve_parted(
        &mut self, 
        ind: usize,
        part_ind: usize, 
        cl_data_ind: usize,
        not_missing: &mut Vec<(usize,usize)>,
        substituted_parts: &mut Vec<HashMap<usize,usize>>,
        parts: &mut Vec<Vec<ClauseData>>, 
        proof_pool: &mut PrimitivePool
    ) -> (){
        let part = &mut parts[part_ind];
        let substituted = &mut substituted_parts[part_ind];
        match self.proof.commands[ind].clone(){
            ProofCommand::Step(ps) =>{
                for i in 0..not_missing.len(){
                    if substituted.contains_key(&not_missing[i].1){
                        not_missing[i].1 = *substituted.get(&not_missing[i].1).unwrap();
                    } 
                }
                //println!("Subs {:?}", substituted);
                let args_op = self.generic_get_args(ind, not_missing, proof_pool);
                match args_op{
                    Some(args)=>{
                        let premises = Self::generic_build_premises(&self.proof.commands, not_missing.clone());
                        let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args, proof_pool);
                        match resolution{
                            Ok(r) => {
                                let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                                let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                                if let ProofCommand::Step(pps) = &mut part[cl_data_ind].data{
                                    pps.args = args;
                                    pps.clause = resolvent;
                                }
                            },
                            _ => {
                                println!("Error: Clauses couldn't be resolved");
                                println!("Resolving for {:?} on part {:?}", ind, part_ind);
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


    fn generic_re_resolve(
        &mut self, 
        ind: usize, 
        not_missing: &mut Vec<(usize,usize)>,
        substituted: &HashMap<usize,usize>, 
        proof_pool: &mut PrimitivePool
    ) -> (){
        match self.proof.commands[ind].clone(){
            ProofCommand::Step(ps) =>{
                for i in 0..not_missing.len(){
                    if substituted.contains_key(&not_missing[i].1){
                        not_missing[i].1 = *substituted.get(&not_missing[i].1).unwrap();
                    } 
                }
                //println!("Subs {:?}", substituted);
                let args_op = self.generic_get_args(ind, not_missing, proof_pool);
                match args_op{
                    Some(args)=>{
                        let premises = Self::generic_build_premises(&self.proof.commands, not_missing.clone());
                        let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args, proof_pool);
                        match resolution{
                            Ok(r) => {
                                let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                                let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                                if let ProofCommand::Step(pps) = &mut self.proof.commands[ind]{
                                    pps.args = args;
                                    pps.clause = resolvent;
                                }
                            },
                            _ => println!("Error: Clauses couldn't be resolved")
                        }
                    }
                    None => println!("Error: arguments couldn't be found")
                }
            }
            _ => ()
        }
    }


    fn build_premises(commands: &Vec<ProofCommand>, left: usize, right: usize)->Vec<Premise> {
        let mut ans: Vec<Premise> = vec![];
        ans.push(Premise::new((0,left),&commands[left]));
        ans.push(Premise::new((0,right),&commands[right]));
        ans
    }

    fn generic_build_premises(commands: &Vec<ProofCommand>, not_missing: Vec<(usize,usize)>)->Vec<Premise> {
        let mut ans: Vec<Premise> = vec![];
        for i in not_missing{
            ans.push(Premise::new((0,i.1),&commands[i.1]));
        }
        ans
    }

    /*fn local_resolution(
        &self, 
        left: usize, 
        right: usize, 
        args: &Vec<ProofArg>, 
        proof_pool: &mut PrimitivePool
    ) -> Vec<Rc<Term>>{
        let command_left = &self.proof.commands[left];
        let command_right = &self.proof.commands[right];
        let mut terms_left: Vec<Rc<Term>> = vec![];
        let mut terms_right: Vec<Rc<Term>> = vec![];
        match command_left{
            ProofCommand::Step(ps_left) => terms_left = ps_left.clause.clone(),
            ProofCommand::Assume{term,..} => terms_left.push(term.clone()),
            ProofCommand::Subproof(_) => ()
        }
        match command_right{
            ProofCommand::Step(ps_right) => terms_right = ps_right.clause.clone(),
            ProofCommand::Assume{term, ..} => terms_right.push(term.clone()),
            ProofCommand::Subproof(_) => ()
        }
        let mut terms_set: HashSet<_> = terms_left.into_iter().collect();
        terms_set.extend(terms_right);
        match &args[0]{
            ProofArg::Term(arg_term) => {
                terms_set.remove(arg_term);
                terms_set.remove(&proof_pool.add(
                    Term::Op(Operator::Not, vec![arg_term.clone()])
                ));
                ()
            },
            ProofArg::Assign(_, arg_term) => {
                terms_set.remove(&arg_term);
                terms_set.remove(&proof_pool.add(
                    Term::Op(Operator::Not, vec![arg_term.clone()])
                ));
                ()
            }
        }
        let terms: Vec<_> = terms_set.into_iter().collect();
        terms
    }*/
    
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

    /*pub fn compute_arguments(&self, proof_pool: &mut PrimitivePool) -> (){
        let mut iter = self.proof.iter();
        while let Some(command) = iter.next(){
            match command{
                ProofCommand::Step(step) => self.elaborate_step(step, proof_pool, &iter),
                ProofCommand::Assume { id, term } => (),
                _ => ()
            }
        }
    }

    fn elaborate_step(&self, step: &ProofStep, proof_pool: &mut PrimitivePool, iter: &ProofIter,) -> (){
        let premises: Vec<_> = step
                .premises
                .iter()
                .map(|&p| {
                    let command = iter.get_premise(p);
                    Premise::new(p, command)
                })
                .collect();
            
        let discharge: Vec<_> = step
            .discharge
            .iter()
            .map(|&i| iter.get_premise(i))
            .collect();

        let rule_args = RuleArgs {
            conclusion: &step.clause, //
            premises: &premises, //
            args: &step.args,
            pool: proof_pool,
            context: &mut self.context,
            previous_command: None, 
            discharge: &discharge, //
            polyeq_time: &mut polyeq_time,
        };
    }
*/
    /*pub fn play(&'a mut self, _pool: &mut PrimitivePool) -> (){
        let (
            units_queue, 
            del,
            ) = self.generic_collect_units();
        println!("Queue: \n{:?}",&units_queue);
        println!("Deleted: \n{:?}",&del);

        let substituted = self.generic_fix_broken_proof(del,_pool);
        println!("Substituted");
        println!("{:?}",substituted);
        self.print();
        println!("Reinserting");
        self.generic_reinsert_units(units_queue, &substituted, _pool);
        self.rebuild(&substituted);
        self.print();
        ()
    }*/

    pub fn pipeline(&'a mut self, _pool: &mut PrimitivePool) -> u8{
        match self.compress(_pool){
            Err(_) => 1,
            Ok(()) => 0
        }
    }

}