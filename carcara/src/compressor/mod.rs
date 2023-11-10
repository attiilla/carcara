//use ahash::{AHashMap, AHashSet};
//use indexmap::IndexMap;
//use indexmap::IndexSet;
use crate::ast::*;
use std::collections::{HashSet, HashMap};
use multiset::HashMultiSet;
use crate::checker::rules;


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
            current_root: ProofCompressor::get_original_root(&p),
        }
    }

    pub fn get_original_root(p: &Proof) -> usize{
        p.commands.len()-1
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

    fn increment_conclusions(
        &self,
        index: usize, 
        conclusions_lists: &Vec<HashSet<usize>>, 
        top_down_queue: &mut Vec<usize>,
        wait_list: &mut HashMultiSet<usize>
    ) -> (){
        for j in &conclusions_lists[index]{
            if let ProofCommand::Step(pss) = &self.proof.commands[*j]{
                wait_list.insert(*j);
                if wait_list.count_of(j) == pss.premises.len(){
                    top_down_queue.push(*j);
                    wait_list.remove_times(j, pss.premises.len());
                }
            }
        }
    }


    fn substitute_node_by_parent(
        &mut self,
        ind: usize,
        unitary_parent_ind: usize,
        substituted: &mut HashMap<usize,usize>
    ) -> (){
        if let ProofCommand::Step(node) = &self.proof.commands[ind]{
            let mut substitute = node.premises[(unitary_parent_ind+1)%2].1;
            if substituted.contains_key(&substitute){//while provavelmente desnecessário e poderia ser um if, conferir depois
                substitute = *substituted.get(&substitute).unwrap();
            }
            substituted.insert(ind, substitute);
        }
    }


    pub fn compress(&mut self)->(){
        let (mut collected_queue, mut deleted_nodes, mut conclusion_lists)  = self.collect_units();
        self.fix_broken_proof(&deleted_nodes, &conclusion_lists);
        ()
        //self.reinsert_units(units_queue);
    }

    fn collect_units(&self) -> (Vec<usize>, HashSet<usize>, Vec<HashSet<usize>>){
        let mut units_queue: Vec<(usize, usize)> = Vec::new();
        let mut marked: HashSet<usize> = HashSet::new();
        let mut conclusion_lists: Vec<HashSet<usize>> = vec![];
        for _ in 0..self.proof.commands.len(){
            conclusion_lists.push(HashSet::new());
        }
        self.recursive_collect_units(self.current_root, &mut marked, &mut units_queue, &mut conclusion_lists);
        let mut deleted: HashSet<usize> = HashSet::new();
        let mut cleaned_queue: Vec<usize> = Vec::new();
        for (i,j) in &units_queue{
            if j>&1 {               //the if ensures the node has more than one child
                cleaned_queue.push(*i);
                deleted.insert(*i);
                ()
            }
        }
        (cleaned_queue, deleted, conclusion_lists)
    }

    fn recursive_collect_units(
        &self, 
        node: usize, 
        marked: &mut HashSet<usize>, 
        units_queue: &mut Vec<(usize, usize)>,
        conclusion_lists: &mut Vec<HashSet<usize>>
    ) -> (){
        match &self.proof.commands[node]{
            ProofCommand::Assume{..} => {
                //This node will always be unary, because if it wasn't unary, the next step of the proof
                //would have to be derived through the "or" rule, and if it was derived through the or rule,
                //this function wouldn't be rescursivelly called for this node
                let last_occur_position = units_queue.iter().rposition(|&(aux, _)| aux == node);
                match last_occur_position{              
                    None => {
                        units_queue.push((node,1));
                    },                     
                    Some(position) =>{
                        let mut not_wrong_position: bool = true;
                        for i in marked.iter(){
                            if units_queue.iter().skip(position+1).any(|(aux,_)| aux==i){
                                not_wrong_position = false;
                                let childs_number = units_queue[position].1;
                                units_queue.push((node,childs_number+1));                         
                                units_queue[position].1 = 0;
                                break;
                            }
                        }
                        if not_wrong_position {
                            units_queue[position].1 += 1;
                        }
                    }
                }
            },
            ProofCommand::Subproof(_) => (/*Not handled yet*/),
            ProofCommand::Step(ps) => {
                if ps.clause.len()==1{
                    let last_occur_position = units_queue.iter().rposition(|&(aux, _)| aux == node);
                    match last_occur_position{              
                        None => {                               //The case where the current node was never saw before
                            units_queue.push((node,1));
                        },                     
                        Some(position) =>{
                            let mut not_wrong_position: bool = true;
                            for i in marked.iter(){                                          //If any marked node is found after the last occurrence   
                                if units_queue.iter().skip(position+1).any(|(aux,_)| aux==i){//of the current node, the node is added to the end of
                                    not_wrong_position = false;                                      //the queue with the value of childs incremented, then
                                    let childs_number = units_queue[position].1;              //the previously active register becomes inactive
                                    units_queue.push((node,childs_number+1));                         
                                    units_queue[position].1 = 0;
                                    break;
                                }
                            }
                            if not_wrong_position {
                                units_queue[position].1 += 1;
                            }
                        }
                    }
                    marked.insert(node);
                }

                
                for (_,i) in &ps.premises{
                    conclusion_lists[*i].insert(node);
                    if ps.rule!="or"{
                        self.recursive_collect_units(*i, marked, units_queue, conclusion_lists);
                    }
                }
                
                marked.remove(&node);
            }
        }
    }

    fn fix_broken_proof(
        &mut self,
        deleted: &HashSet<usize>, 
        conclusion_lists: &Vec<HashSet<usize>>
    )-> (){
        let mut top_down_queue = self.assumes();
        let mut wait_list: HashMultiSet<usize> = HashMultiSet::new();
        let mut substituted: HashMap<usize,usize> = HashMap::new();
        for ind in 0..self.proof.commands.len() {
            let i = top_down_queue[ind];
            println!("\nfixing {:?}",i);
            let access = &self.proof.commands;
            match &access[i]{
                ProofCommand::Assume { .. } => {
                    self.increment_conclusions(i, conclusion_lists, &mut top_down_queue, &mut wait_list);
                    //println!("We are in an assume node");
                },
                ProofCommand::Step(ps) => {
                    self.increment_conclusions(i, conclusion_lists, &mut top_down_queue, &mut wait_list);
                    //println!("We are in an proof step node");
                    let premises_clone = ps.premises.clone();
                    let mut deleted_parent_flag = false;
                    for parent in 0..premises_clone.len(){ 
                        if deleted.contains(&premises_clone[parent].1){
                            deleted_parent_flag = true;
                            println!("There is an deleted parent in this node: {:?}", &premises_clone[parent].1);
                            self.substitute_node_by_parent(i, (parent+1)%2, &mut substituted);
                        }
                    }
                    if !deleted_parent_flag{
                        //self.re_resolve(i, &substituted);
                    }

                }
                ProofCommand::Subproof(_) => (/*Not handled yet*/),
            }
        }
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

    /*fn find_arguments(&self, i: usize, j: usize)->(){
        let terms: [Vec<Rc<Term>>;2] = [
        self.extract_term(&self.proof.commands[i]),
        self.extract_term(&self.proof.commands[j])];
        let left_terms_with_parity: Vec<usize,&Rc<Term>> = terms[0].iter().map(|x| x.remove_all_negations_with_polarity()).collect();
        let right_terms_with_parity = terms[1].iter().map(|x| x.remove_all_negations_with_polarity()).collect();
        let left_set: HashSet<(u32, &Rc<Term>)> = left_terms_with_parity.into_iter().map(|(_,b)| b).collect();
        //let pivot = right_terms_with_parity.iter().find(|(x,y)| 
        //    left_set.iter().any(|(a,b)| 
        //            compare_possible_pivot(*x,y))).unwrap();
        println!("marca");
    }*/


    pub fn find_args(&self,i: usize, j: usize) -> (Rc<Term>,bool){
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
        let parity_pivot = non_negated_terms_right.into_iter().find(|&x| 
                                                    aux_set.iter().any(|&y| 
                                                            compare_possible_pivot(x,y))).unwrap();
        let order_arg: bool = parity_pivot.0%2!=0;
        let pivot = parity_pivot.1.clone();
        return (pivot, order_arg)
    }


    pub fn play(&mut self) -> (){
        let mut node;
        for i in 0..self.proof.commands.len(){
            node = &self.proof.commands[i];
            match node{
                ProofCommand::Assume { id, term } => println!("{:?}: Assume {:?}",id,term),
                ProofCommand::Step(ps) => println!("{:?}: {:?}({:?}) = {:?} (Arguments: {:?})",
                ps.id, ps.rule, ps.premises, ps.clause, ps.args),
                ProofCommand::Subproof(_) => ()
            }
        }
        let ans = self.find_args(9,5);
        //println!("terms1: {:?}\nterms2: {:?}",ans[0],ans[1]);
        println!("{:?}",ans);
    }
}