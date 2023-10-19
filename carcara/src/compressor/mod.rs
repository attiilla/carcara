//use ahash::{AHashMap, AHashSet};
//use indexmap::IndexMap;
use indexmap::IndexSet;
use crate::ast::*;
use std::collections::HashSet;

#[derive(Debug)]
pub struct ProofCompressor<'a>{
    original_proof: &'a Proof,
    proof: Proof,
    current_root: usize,
//    pub compression_steps: Vec<CompressionAlgorithms>,
}

impl<'a> ProofCompressor<'a>{
    pub fn new(p: &Proof)->ProofCompressor{
        ProofCompressor{
        original_proof: &p,
        proof: p.clone(),
        current_root: ProofCompressor::get_original_root(&p)
        }
    }

    fn get_original_root(p: &Proof) -> usize{
        p.commands.len()-1
    }

    /*pub fn compress(&mut self)->(){
        let mut units_queue  = self.collect_units();
        self.fix_broken_proof(&self.original_root_id());
        self.reinsert_units(units_queue);
    }*/

    pub fn collect_units(&self) -> (Vec<(usize, usize)>, Vec<bool>){
        let mut units_queue: Vec<(usize, usize)> = Vec::new();
        let mut marked: HashSet<usize> = HashSet::new();
        self.recursive_collect_units(self.current_root, &mut marked, &mut units_queue);
        let mut deleted: Vec<bool> = vec![false;self.proof.commands.len()];
        for (i,j) in &units_queue{
            if j>&1 {deleted[*i] = true}; //the if ensures the node has more than one child
        }
        (units_queue, deleted)
    }

    pub fn recursive_collect_units(
            &self,
            node: usize, 
            marked: &mut HashSet<usize>, 
            units_queue: &mut Vec<(usize, usize)>
        ) -> (){
        match &self.proof.commands[node]{
            ProofCommand::Assume{..} => (),
            ProofCommand::Subproof(_) => (/*Not handled yet*/),
            ProofCommand::Step(ps) => {
                if ps.clause.len()==1{
                    let last_occur_position = units_queue.iter().rposition(|&(aux, _)| aux == node);
                    match last_occur_position{
                        None => units_queue.push((node,1)),                     //The case where the current node never war saw before
                        Some(position) =>{
                            for i in marked.iter(){                                          //If any marked node is found after the last occurrence of the
                                if units_queue.iter().skip(position+1).any(|(aux,_)| aux==i){//current node, the node is added to the end of the queue
                                    let childs_number = units_queue[position].1;              //with the value of childs incremented, then
                                    units_queue.push((node,childs_number+1));                        //the previously active register becomes inactive 
                                    units_queue[position].1 = 0;                              
                                    break;
                                }
                            }
                        }
                    }
                    println!("{:?}",units_queue);
                    marked.insert(node);
                    for (_,i) in &ps.premises{
                        self.recursive_collect_units(*i, marked, units_queue);
                    }
                    marked.remove(&node);
                }
            }
        }
    }


    /*
    pub fn collect_units(&mut self) -> Vec<usize, usize>{
        let mut units_queue: Vec<usize, usize> = Vec::new();
        //let mut visited: Vec<bool> = vec![false,self.original_proof.commands.len()];
        let mut marked: AHashSet<usize> = AHashSet::new();
        let mut dfs_stack: Vec<usize> = Vec::new();
        let mut current_node: usize;
        dfs_stack.push(self.current_root);
        while !dfs_stack.is_empty(){
            current_node = dfs_stack.pop().unwrap();
            match self.proof.commands[current_node] {
                ProofCommand::Assume{..} => (),
                ProofCommand::Subproof(_) => (/*Not handled yet*/),
                ProofCommand::Step(ps) => {
                    for &(_,k) in ps.premises{
                        dfs_stack.push(k);
                    }
                    if ps.clause.len()==1{ //checks if clause is unary
                        let last_occur_position = units_queue.iter().rposition(|&(aux, _)| aux == current_node);
                        for i in marked{
                            if units_queue.iter().skip(last_occur_position+1).any(|&(aux,_)| aux==i){//If any marked node is found after the last occurrence of the
                                let child_number = units_queue[last_occur_position].1;               //current_node, the current node is moved to the end of the queue and
                                units_queue.push((current_node,child_number+1));                     //the previously active register becomes inactive
                                units_queue[last_occur_position].1 = 0;
                                break;
                            }
                        }
                        marked.insert(current_node);
                    }
                }
            }
        }
        units_queue
    }
    */
}