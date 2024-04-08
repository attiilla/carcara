
//BUG: reinsert_units_parted assumes the unit isn't substituted
//BUG: generalize function generic_get_args_parted to not expect ordered premises
//BUG?: non-resolution chain will be handled by allowing clauses of a part to point to clauses in another part
//OPT: Implement reinsert_units_parted with at maximum one resolution for each part
//OPT: The PartTracker vectors can use less space if split in two variables
//OPT: write lifetime anotations to make found_clauses use references as keys in rebuild_parted
//WARN: assume after steps

use crate::ast::*;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;
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
            ProofCommand::Assume { term,.. } => println!("Clause: {:?}", term),
            ProofCommand::Step(ps) => {
                println!("Clause: {:?}", &ps.clause);
                println!("Local Premises: {:?}", &part[i].local_premises);
                println!("Global Premises: {:?}", &ps.premises);
            },
            _ => ()
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

    fn substitute_node_by_parent_parted(
        ind: usize,
        unitary_parent_ind: usize,
        substituted: &mut HashMap<usize,usize>
    ) -> (){
        let mut substitute = unitary_parent_ind;
        if substituted.contains_key(&substitute){
            substitute = *substituted.get(&ind).unwrap();
        }
        substituted.insert(ind, substitute);
    }


    fn substitute_node_by_parent_old(//working fine if the proof has only 'resolutions' and 'or' rules
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
        match self.compress_parted(_pool){
            Err(e) => {
                println!("Error");
                match e{
                    CompressionError::Collection(_) => println!("There is no collectable clauses."),
                    CompressionError::SubproofNotImplementedYet => (),//println!("The logic to compress subproofs is yet to be implemented."),
                    CompressionError::ResolutionError(res) => println!("There was an error when resolving the clauses {:?}.",res),
                }
            }
            Ok(()) => ()
        }
        ()
    }
/*
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
    }*/

    pub fn compress_parted(&'a mut self, _pool: &mut PrimitivePool) -> Result<(),CompressionError>{
        //env::set_var("RUST_BACKTRACE", "1");
        //self.print();
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
                self.reinsert_units_parted(&mut parts, part_units_queue, &substituted_in_parts, referenced_by_parts, _pool);
                //print_part(&parts[2], Some(2));
                //println!("");
                self.rebuild_parted(substituted_in_parts,parts);
                let _ = print_proof(&self.proof.commands, true);
            }/*
            for i in 0..parts.len(){
                parts[i].reverse();
                self.local_premises_computation(i, &mut parts);
            }*/
        };
        Ok(())
    }

    pub fn collect_units_parted(&self)->
        Result<(Vec<Vec<ClauseData>>,
        Vec<HashSet<usize>>,
        Vec<Vec<usize>>,
        Vec<PartTracker>), CollectionError>
    {
        let n = self.proof.commands.len();
        let mut parts: Vec<Vec<ClauseData>> = vec![Vec::new(),Vec::new()];
        //position i stores all parts that contain the current node i and how many times this node is used inside that part
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
                            if ps.rule!="or" {
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
                                referenced_by_parts[ps.premises[0].1].insert(0);
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
                    //println!("{:?} Partslen: {:?}",i,&parts.len());
                }
                ProofCommand::Subproof(_) => (),
            }
            
        }
        //println!("check0");
        /*for i in 0..parts.len(){
            print_part(&parts[i], Some(i));
            println!("");
        }*/
        //println!("check1");
        //println!("Parts units queue: {:?}", &part_units_queue);
        //println!("Parts deleted: {:?}",&part_deleted);
        /*println!("Coming from resolution: {:?}",&coming_from_resolution);*/
        //println!("Referenced by parts: {:?}",&referenced_by_parts);
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
            parts[current_part_id].reverse();
            self.local_premises_computation(current_part_id, parts);
            /*for j in 0..parts[current_part_id].len(){
                println!("{:?}-{:?}:  {:?}", current_part_id, j, &parts[current_part_id][j])
            }*/
            //println!("\n\n");
            if part_deleted[current_part_id].len()>0{
                for cl_data_ind in 0..parts[current_part_id].len(){
                    let current_clause = &parts[current_part_id][cl_data_ind];
                    match &current_clause.data{
                        ProofCommand::Assume {..} => (),
                        ProofCommand::Step(ps) => {
                            let mut not_missing_index: Vec<(usize, usize)> = Vec::new();
                            let aux = &current_clause.local_premises;
                            for j in 0..aux.len(){
                                let true_index = &(parts[current_part_id][aux[j]].index as usize);
                                if !part_deleted[current_part_id].contains(true_index){
                                    //println!("for {:?} pushed {:?}", &cl_data_ind, (&j,&aux[j]));
                                    not_missing_index.push((j,aux[j]));
                                }
                            }
                            if not_missing_index.len()==1 && (&ps.rule=="resolution"||&ps.rule=="th-resolution"){
                                Self::substitute_node_by_parent_parted(
                                    cl_data_ind,
                                    not_missing_index[0].1,
                                    &mut substituted_in_parts[current_part_id]
                                );
                            } else {
                                if not_missing_index.len()!=current_clause.local_premises.len()  || not_missing_index.iter().any(|(_,key)| substituted_in_parts[current_part_id].contains_key(key)){
                                    self.generic_re_resolve_parted(
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
        Ok(substituted_in_parts)
    }



    fn reinsert_units_parted(
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
                //println!("current part {current_part}: Checked");
                let mut part = &mut parts[current_part];
                let mut current_root = part.len()-1;
                let substituted = &substituted_in_parts[current_part];
                if substituted.contains_key(&current_root){
                    current_root = *substituted.get(&current_root).unwrap();
                }
                let units_queue = &part_units_queue[current_part];
                for &u in units_queue{
                    let mut args_op: Vec<ProofArg> = Vec::new();
                    let mut unit = u;
                    if substituted.contains_key(&unit){
                        unit = *substituted.get(&unit).unwrap();
                    }
                    //println!("unit {unit} and root {current_root}");
                    match &self.proof.commands[unit]{
                        ProofCommand::Assume { term,.. } => {
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
                    
                    if args_op.len()!=0{
                        let mut unit_part_ind = *referenced_by_parts[unit].inv_index.get(&current_part).unwrap();
                        unit_part_ind = Self::mirror_inverse_index(unit_part_ind, part.len());
                        //println!("unit_part_ind {unit_part_ind}; current_part {current_part}");
                        let premises = Self::generic_build_premises_parted(part, vec![(0,current_root),(0,unit_part_ind)]);
                        //Self::build_premises(&self.proof.commands, current_root, unit);
                        let nc: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args_op, proof_pool);
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
                                    local_premises: vec![current_root, unit_part_ind]
                                });
                                //println!("New node premises {:?}", vec![current_root, unit_part_ind]);
                                current_root+=1;
                            },
                            Err(_e) => {
                                println!("checker error");
                                println!("Premises {:?}",&premises);
                                println!("Arguments {:?}",&args_op);
                            }
                        }
                    }
                }
            }
        }
    }


    fn rebuild_parted(
        &mut self, 
        substituted_in_parts: Vec<HashMap<usize,usize>>, 
        parts: Vec<Vec<ClauseData>>
    ) -> (){
        /*for i in 0..parts.len(){
            for j in 0..parts[i].len(){
                println!("{:?}-{:?}:  {:?}", i, j, &parts[i][j])
            }
            let substitutedd = &substituted_in_parts[i];
            println!("Subst {:?}",i);
            for j in substitutedd{
                println!("{:?}",j);
            }
            println!("\n\n");
        }*/
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
                match &part[local_ind].data{
                    ProofCommand::Assume { term,.. } =>{
                        if !found_assertions.contains_key(&term){
                            new_commands.push(ProofCommand::Assume{id: format!("a{assume_ind}"), term: term.clone()});
                            assume_ind += 1;
                            found_assertions.insert(term.clone(),new_commands.len()-1);
                            //println!("{:?}/{:?}-Inserted A {:?}",part_ind,local_ind,&term);
                        }
                    }
                    ProofCommand::Step(ps) => {
                        //println!("ps {:?},{:?}",&ps.clause,&ps.premises);
                        if !found_clauses.contains_key(&ps.clause) && !substituted.contains_key(&local_ind){
                            let mut formated_prem: Vec<(usize,usize)> = vec![];
                            if &part[local_ind].local_premises.len()>&0{
                                //println!("Entrou em {local_ind}");
                                //println!("{:?}",&part[local_ind].local_premises);
                                for &premm in &part[local_ind].local_premises{
                                    let mut prem = premm;
                                    if substituted.contains_key(&prem){
                                        prem = *substituted.get(&prem).unwrap();
                                    }
                                    match &part[prem].data{
                                        ProofCommand::Assume { id, term } => {
                                            formated_prem.push((0, *found_assertions.get(term).unwrap()));
                                        }
                                        ProofCommand::Step(pps) => {
                                            formated_prem.push((0, *found_clauses.get(&pps.clause.clone()).unwrap()));
                                        }
                                        ProofCommand::Subproof(_) => ()
                                    }
                                }
                            } else {
                                //construct a vector analogue to the local premises in the block above
                                if let ProofCommand::Step(pps) = &self.proof.commands[part[local_ind].index as usize]{
                                    let analogue = &pps.premises;
                                    for &(_, prem) in analogue{
                                        match &self.proof.commands[prem]{
                                            ProofCommand::Assume { id, term } =>
                                                formated_prem.push((0, *found_assertions.get(term).unwrap())),
                                            ProofCommand::Step(p3s) => 
                                                formated_prem.push((0, *found_clauses.get(&p3s.clause.clone()).unwrap())),
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
                            //println!("{:?}/{:?}-Inserted T {:?}",part_ind,local_ind,ps.clause.clone());
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

    /*fn reinsert_units_parted(
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
    }*/

    fn local_premises_computation(
        &self,
        ind: usize,
        parts: &mut Vec<Vec<ClauseData>>
    )->(){
        let part = &parts[ind];
        /*if ind==2 || ind==1{
            for i in 0..part.len(){
                println!("{:?}-{:?}: {:?}",ind,i,part[i]);
            }
            println!("\n\n");
        }*/

        //map from the global index of a clause to the local index of every clause that uses it as a premise 
        //the first element of the pair is the order in which the premise is used by the clause
        let mut table_prem: HashMap<usize, Vec<(usize,usize)>> = HashMap::new();

        //map from global index to local index
        let mut table_pos: HashMap<usize, usize> = HashMap::new();
        
        let mut prem_length: Vec<usize> = vec![];
        for i in 0..part.len(){
            let key = part[i].index as usize;
            table_pos.insert(key, i);
            
            match &part[i].data{
                ProofCommand::Step(ps) => {
                    let mut j = 0;
                    for (_,p) in &ps.premises{
                        table_prem.entry(*p).or_insert_with(Vec::new).push((j,key));
                        j+=1;
                    }
                    if ps.rule!="resolution" && ps.rule!="th-resolution"{
                        prem_length.push(0);
                    } else{
                        prem_length.push(ps.premises.len());
                    }
                    
                }
                _  => prem_length.push(0)
            }
        }/*
        if ind==2 || ind==1{        
            println!("table_pos: {:?}",table_pos);
            println!("table_prem: {:?}",table_prem);
            println!("pl: {:?}",&prem_length);
        }*/

        
        let mut mut_part = &mut parts[ind];
        for i in 0..mut_part.len(){
            mut_part[i].local_premises = vec![0;prem_length[i]];
        }
        for i in 0..mut_part.len(){
            let key = mut_part[i].index as usize;
            
            if table_prem.contains_key(&key){
                for &(ord,pr) in table_prem.get(&key).unwrap(){
                //println!("{:?} to {:?}",pr,table_pos.get(&pr).unwrap());
                    let mut loc_prem = &mut mut_part[*table_pos.get(&pr).unwrap()].local_premises;
                    loc_prem[ord] = i;
                }
            }
        }     
        /*if ind==2 || ind==1{
            for i in 0..mut_part.len(){
                println!("{:?}-{:?}: {:?}",ind,i,mut_part[i]);
            }
            println!("\n\n");
        }*/
        
        
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


    pub fn generic_get_args_parted(
        part: &Vec<ClauseData>, 
        ind: usize, 
        not_missing: &Vec<(usize,usize)>
    ) -> Option<Vec<ProofArg>>{
        /*println!("ind {ind}");
        println!("not mia: {:?}",not_missing);
        for i in 0..part.len(){
            println!("{:?} - {:?}",i,part[i]);
        }*/
        if let ProofCommand::Step(ps) = &part[ind].data{
            let mut arg_vec: Vec<ProofArg> = Vec::new();
            //println!("Args: {:?}",&ps.args);
            //println!("Non missing: {:?}",&not_missing);
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
        part_ind: usize, 
        cl_data_ind: usize,
        not_missing: &mut Vec<(usize,usize)>,
        substituted_parts: &mut Vec<HashMap<usize,usize>>,
        parts: &mut Vec<Vec<ClauseData>>, 
        proof_pool: &mut PrimitivePool
    ) -> (){
        let mut part = &mut parts[part_ind];
        let substituted = &mut substituted_parts[part_ind];
        match &mut part[cl_data_ind].data{
            ProofCommand::Step(ps) =>{
                for i in 0..not_missing.len(){
                    if substituted.contains_key(&not_missing[i].1){
                        not_missing[i].1 = *substituted.get(&not_missing[i].1).unwrap();
                    } 
                }
                let args_op = Self::generic_get_args_parted(part, cl_data_ind, not_missing);
                match args_op{
                    Some(args)=>{
                        let premises = Self::generic_build_premises_parted(part, not_missing.clone());
                        let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args, proof_pool);
                        match resolution{
                            Ok(r) => {
                                let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                                let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                                if let ProofCommand::Step(pps) = &mut part[cl_data_ind].data{
                                    //println!("Changing");
                                    pps.args = args;
                                    pps.clause = resolvent;
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

    fn generic_build_premises_parted(part: &Vec<ClauseData>, not_missing: Vec<(usize,usize)>)->Vec<Premise> {
        let mut ans: Vec<Premise> = vec![];
        for i in not_missing{
            ans.push(Premise::new((0,i.1),&part[i.1].data));
        }
        ans
    }

    fn mirror_inverse_index(ind: usize, length: usize)->usize{
        length-ind-1
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


}