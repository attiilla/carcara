//use ahash::{AHashMap, AHashSet};
//use indexmap::IndexMap;
//use indexmap::IndexSet;
use crate::ast::*;
use std::collections::{HashSet, HashMap};
//use std::thread::current;
//use multiset::HashMultiSet;
use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution, unremove_all_negations};
use crate::checker::error::CheckerError;
use std::sync::Arc;
use std::env;



#[derive(Debug)]
pub struct ProofCompressor<'a>{
    pub _original_proof: &'a Proof,
    proof: Proof,
    current_root: usize,
//    pub compression_steps: Vec<CompressionAlgorithms>,
}

impl<'a> ProofCompressor<'a>{
    pub fn new(p: &Proof)->ProofCompressor{
        ProofCompressor{
            _original_proof: &p,
            proof: p.clone(),
            current_root: p.commands.len()-1,
        }
    }


    pub fn assumes(&self) -> Vec<usize>{
        let mut assumes_vec: Vec<usize> = Vec::new();
        for i in 0..self.proof.commands.len(){
            match self.proof.commands[i]{
                ProofCommand::Assume{..} => assumes_vec.push(i),
                _ => ()
            }
        }
        assumes_vec
    }

    fn substitute_node_by_parent(
        &self,
        ind: usize,
        unitary_parent_ind: usize,
        substituted: &mut HashMap<usize,usize>
    ) -> (){
        if let ProofCommand::Step(node) = &self.proof.commands[ind]{
            let mut substitute = node.premises[(unitary_parent_ind+1)%2].1;
            if substituted.contains_key(&substitute){
                substitute = *substituted.get(&substitute).unwrap();
            }
            //println!("substituindo {ind} por {substitute}, miss_ind = {unitary_parent_ind}");
            substituted.insert(ind, substitute);
        }
    }

    pub fn smart_compress(&mut self, proof_pool: &mut PrimitivePool) -> (){
        env::set_var("RUST_BACKTRACE", "1");
        let (
            mut units_queue, 
            mut deleted, 
            mut conclusions
            ) = self.smart_collect_units();
            //println!("units queue: \n{:?}\n", units_queue);
            //println!("deleted: \n{:?}\n", deleted);
            //println!("conclusions: \n{:?}\n", conclusions);
            //println!("Proof after collect units:");
            //self.print();
            //println!("Passamos do Collect Units");
            let substituted = self.smart_fix_broken_proof(deleted,proof_pool);
            //println!("Substituted: {:?}", &substituted);
            //println!("Proof after fix:");
            //self.print();
            //println!("Inserting:");
            self.reinsert_units(units_queue, &substituted, proof_pool);
            //println!("Proof after inserting:");
            //self.print();
            //println!("Post-processing");
            self.rebuild(&substituted);
            //println!("Done");
            self.print();
            let a = print_proof(&self.proof.commands, true);
    }

    fn smart_collect_units(&self)->(Vec<usize>, HashSet<usize>, Vec<Vec<usize>>){
        let mut units_queue: Vec<usize> = vec![]; 
        let mut deleted: HashSet<usize> = HashSet::new(); 
        let mut not_mark: HashSet<usize> = HashSet::new(); 
        let mut conclusion_lists: Vec<Vec<usize>> = vec![];
        for _ in 0..self.proof.commands.len(){
            conclusion_lists.push(Vec::new());
        }
        for i in (0..self.proof.commands.len()).rev(){
            let pc = &self.proof.commands[i];
            match pc{
                ProofCommand::Assume{..} => {
                    if !not_mark.contains(&i){
                        units_queue.push(i);
                        deleted.insert(i);
                    }
                }
                ProofCommand::Step(ps) => {
                    for (_,j) in ps.premises.clone(){
                        conclusion_lists[j].push(i);
                    }
                    if ps.rule=="or"{
                        not_mark.insert(ps.premises[0].1);
                    }
                    if ps.clause.len()==1 && conclusion_lists[i].len()>1{
                        units_queue.push(i);
                        deleted.insert(i);
                    }
                }
                ProofCommand::Subproof(_) => ()
            }
        }
        return (units_queue, deleted, conclusion_lists)
    }

    fn smart_fix_broken_proof(
        &mut self,
        deleted: HashSet<usize>,
        proof_pool: &mut PrimitivePool 
    )->HashMap<usize, usize>/*()*/{
        let mut substituted: HashMap<usize, usize> = HashMap::new();
        //let mut i = 0;
        //for pc in self.proof.commands.iter(){
        for i in 0..self.proof.commands.len(){
            match &self.proof.commands[i]{
                ProofCommand::Assume {..} => (),
                ProofCommand::Step(ps) => {
                    let mut missing_index: Option<usize> = None;
                    let aux = ps.premises.clone();
                    for j in 0..aux.len(){
                        if deleted.contains(&aux[j].1){
                            missing_index = Some(j);
                        }
                    }
                    if aux.len()!=1{
                        match missing_index{
                            None => self.re_resolve(i, &substituted, proof_pool),
                            Some(miss_ind) => self.substitute_node_by_parent(i,miss_ind, &mut substituted),
                        }
                    }
                }
                ProofCommand::Subproof(_) => ()
            }
        }
        substituted
    }

    fn reinsert_units(
        &mut self,
        units_queue: Vec<usize>,
        substituted: &HashMap<usize,usize>,
        proof_pool: &mut PrimitivePool
    )->(){
        let mut current_root = self.proof.commands.len()-1;
        /*if substituted.contains_key(&current_root){
            current_root = *substituted.get(&current_root).unwrap();
        }*/
        for u in units_queue{
            let mut unit = u;
            if substituted.contains_key(&unit){
                unit = *substituted.get(&unit).unwrap();
            }
            //println!("Resolving with {unit}");
            let args = self.find_args(current_root,unit,proof_pool);
            //let new_clause = self.local_resolution(current_root, unit, &args, proof_pool);
            let premises = Self::build_premises(&self.proof.commands, current_root, unit);
            let nc: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args, proof_pool);
            //println!("resolving {current_root} and {unit}");
            //println!("resolution in reinsert units:\n{:?}",&nc);
            match nc{
                Ok(c) => {
                    let new_clause_set: HashSet<Rc<Term>> = c.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                    let new_clause: Vec<Rc<Term>> = new_clause_set.into_iter().collect();
                    let new_proof_step = ProofStep{
                        id: "".to_string(),
                        clause: new_clause,
                        rule: "resolution".to_string(),
                        premises: vec![(0,current_root),(0,unit)],
                        args,
                        discharge: vec![]
                    };
                    self.proof.commands.push(ProofCommand::Step(new_proof_step));
                    current_root+=1;
                },
                _ => println!("Error")
            }
        }
    }

    fn rebuild(&mut self, substituted: &HashMap<usize,usize>) -> (){
        let mut assume_ind: usize = 0;
        let mut step_ind: usize = 0;
        let mut subproof_ind: usize = 0;
        let mut new_commands: Vec<ProofCommand> = vec![];
        let mut new_index_table: HashMap<usize,usize> = HashMap::new();
        //let mut index: usize = 0;
        for index in 0..self.proof.commands.len(){
            if !substituted.contains_key(&index){
                match &mut self.proof.commands[index]{
                    ProofCommand::Assume{id,term} => {
                        new_commands.push(ProofCommand::Assume{id: format!("a{assume_ind}"), term: term.clone()});
                        assume_ind += 1;
                    }
                    ProofCommand::Step(ps) => {
                        ps.id = format!("t{step_ind}");
                        for (depth, p) in ps.premises.iter_mut() {
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
                        subproof_ind += 1;
                    }
                }
                new_index_table.insert(index,new_commands.len()-1);
            }
        }
        self.proof.commands = new_commands;
    }

    pub fn print(&self)->(){
        for i in &self.proof.commands{
            match i{
                ProofCommand::Assume{id,term} => println!("Assume {:?}: {:?}",id,term),
                ProofCommand::Step(ps) => println!("Resolution {:?}: {:?}->{:?}",ps.id,ps.premises,ps.clause),
                _ => ()
            }
        }
    }
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

    pub fn find_args(&self,i: usize, j: usize, proof_pool: &mut PrimitivePool) -> Vec<ProofArg>{
        //println!("Encontrando argumentos para {i} e {j}");
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
        //println!("Esquerda:{:?}",&non_negated_terms_left);
        let non_negated_terms_right: Vec<(u32, &Rc<Term>)> = terms_right.iter().map(|term| term.remove_all_negations()).collect();
        //println!("Direita:{:?}",&non_negated_terms_right);
        let aux_set: HashSet<(u32, &Rc<Term>)> = non_negated_terms_left.clone().into_iter().collect();
        let pp = non_negated_terms_right.into_iter().find(|&x| 
                                                    aux_set.iter().any(|&y| 
                                                            compare_possible_pivot(x,y)));
        //println!("pp:{:?}",&pp);
        let parity_pivot = pp.unwrap();
        let order_arg: bool = parity_pivot.0%2!=0;
        let pivot = parity_pivot.1.clone();
        let args = vec![ProofArg::Term(pivot), ProofArg::Term(proof_pool.bool_constant(order_arg))];
        return args
    }

    fn re_resolve(
        &mut self, 
        ind: usize, 
        substituted: &HashMap<usize,usize>, 
        proof_pool: &mut PrimitivePool
    ) -> (){
        //println!("Re-resolving clause {ind}");
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

                let args = self.find_args(left_ind,right_ind, proof_pool);
                let premises = Self::build_premises(&self.proof.commands, left_ind, right_ind);
                //let resolvent: Vec<Rc<Term>> = self.local_resolution(left_ind, right_ind, &args, proof_pool);
                let resolution: Result<Vec<(u32, &Rc<Term>)>, CheckerError> = apply_generic_resolution(&premises, &args, proof_pool);
                //println!("resolving {left_ind} and {right_ind}");
                //println!("resolution in re-resolve:\n{:?}",&resolution);
                match resolution{
                    Ok(r) => {
                        let resolvent_set: HashSet<Rc<Term>> = r.into_iter().map(|x| unremove_all_negations(proof_pool,x)).collect();
                        let resolvent: Vec<Rc<Term>> = resolvent_set.into_iter().collect();
                        if let ProofCommand::Step(pps) = &mut self.proof.commands[ind]{
                            pps.args = args;
                            pps.clause = resolvent;
                        }
                    },
                    _ => println!("Error")
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

    fn local_resolution(
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
    }

    pub fn play(&'a mut self, pool: &mut PrimitivePool) -> (){
        let pc = &self.proof.commands[11];
        if let ProofCommand::Step(ps) = pc {
            let tt = ps.clause[0].clone();
            let termo = tt.get_arc();
            let cloned_termo = Arc::clone(termo);
            // Now, you can access the Term inside the cloned Arc
             let term: &Term = &*cloned_termo;
             match term{
                Term::Const(_) => println!("const"),
                Term::Var(_,_) => println!("var"),
                Term::App(_,_) => println!("app"),
                Term::Op(_,_) => println!("op"),
                Term::Sort(_) => println!("sort"),
                Term::Quant(_,_,_) => println!("quant"),
                Term::Choice(_,_) => println!("choice"),
                Term::Let(_,_) => println!("let"),
                Term::Lambda(_,_) => println!("lambda")
             }

        }
    }
}