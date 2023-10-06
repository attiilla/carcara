use ahash::{AHashMap, AHashSet};
use crate::ast::*;
use std::collections::VecDeque;
use std::hash::Hash;

#[derive(Debug)]
pub struct ProofCompressor<'a>{
    original_proof: &'a Proof,
    proof: Proof,
    current_root: (usize,usize),
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

    fn get_original_root(p: &Proof) -> (usize,usize){
        (0,p.commands.len()-1)
    }

    pub fn compress(&mut self)->(){
        let mut units_queue  = self.collect_units();
        self.fix_broken_proof(&self.original_root_id());
        self.reinsert_units(units_queue);
    }

    pub fn collect_units(&mut self) -> VecDeque<((usize,usize), ProofStep)>{
        let mut clauses_numb;
        let mut units_queue: VecDeque<((usize,usize), ProofStep)> = VecDeque::new();
        let mut bfs_queue: VecDeque<(usize,usize)> = VecDeque::new();
        let mut visited: AHashSet<(usize,usize)> = AHashSet::new();
        
        let root_id = ProofCompressor::get_original_root(self.original_proof);
        let mut root_and_premises: Vec<(usize, usize)>;
        match self.original_proof.commands[root_id.1]{
            ProofCommand::Assume{..} => println!("Conclusion is an axiom, impossible to compress"),
            ProofCommand::Step(s) => root_and_premises = s.premises.clone(),
            ProofCommand::Subproof(_) => println!("Subproof not handled yet :( "),
        }
        root_and_premises.push(root_id);
        let mut current_node = Some(root_id);
        while let Some(id) = current_node{  
            if visited.contains(&id) {
              current_node = bfs_queue.pop_front();
            } else {
                match self.proof.commands[id.1]{
                    ProofCommand::Assume { id, term } => (),
                    _ => ()
                }













                // Checks if the rule used to derive this node is distinct from "or"
                // If it is "or", don't put the childs of the node in the queue
                if let ProofCommand::Step(s) = self.proof.commands[id.1]{
                    if s.rule!="or"{
                        //Put the childs of the current_node on the search queue
                        for i in s.premises{
                            bfs_queue.push_back(i);
                        }
                    }
                }
                // Checks if the current_node can get closer to the proof root
                if !root_and_premises.contains(&id){
                    // Checks if the clause of the node is unitary
                    clauses_numb = .clause.len();
                    if clauses_numb==1{
                        self.formated_proof.get_mut(&s).unwrap().deleted = true;
                        let node_data = self.formated_proof.get(&s).unwrap().clone();
                        let mut switch = false;
                        for i in &node_data.premises{
                            let early_child = units_queue.iter().position(|(node_id, _)| node_id==i);
                            match early_child{
                                None => (),
                                Some(u) => {
                                    units_queue.insert(u,(s.clone(),node_data.clone()));
                                    switch = true;
                                },
                            }
                        }
                        if !switch{
                            units_queue.push_back((s.clone(),node_data.clone()));
                        }
                        
                    }
                }
                visited.insert(s.clone());
                current_node = bfs_queue.pop_front();
            }
        }
        units_queue
    }
}