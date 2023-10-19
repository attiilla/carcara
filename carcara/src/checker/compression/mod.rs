use ahash::{AHashMap, AHashSet};
use crate::ast::*;
use std::collections::VecDeque;
use std::hash::Hash;

#[derive(Debug)]
pub struct ProofCompressor<'a>{
    original_proof: &'a Proof,
    proof: Proof,
    current_root: (usize,usize),
    depth: usize,
//    pub compression_steps: Vec<CompressionAlgorithms>,
}

impl<'a> ProofCompressor<'a>{
    pub fn new(p: &Proof, d)->ProofCompressor{
        ProofCompressor{
        original_proof: &p,
        proof: p.clone(),
        depth: d,
        current_root: ProofCompressor::get_original_root(&p)
        }
    }

    fn get_original_root(p: &Proof) -> (usize,usize){
        let n = p.commands.len();
        (self.depth,n)
    }

    pub fn compress(&mut self)->(){
        let mut units_queue  = self.collect_units();
        self.fix_broken_proof(&self.original_root_id());
        self.reinsert_units(units_queue);
    }

    pub fn collect_units(&mut self) -> VecDeque<((usize,usize), ProofStep)>{
        let mut units_queue: AHashMap<(usize, usize), usize> = AHashMap::new();
        let mut visited: AHashSet<(usize, usize)> = AHashSet::new();
        let mut dfs_stack: Vec<(usize, usize)> = Vec::new();
        let mut position: usize = 0;
        let mut node: (usize, usize) = self.current_root;
        if visited.contains(&node) {
            current_node = dfs_stack.pop_back();
          } else {
            for i in self.proof

          }
        units_queue
    }
}