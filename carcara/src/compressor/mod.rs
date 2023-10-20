//use ahash::{AHashMap, AHashSet};
//use indexmap::IndexMap;
use indexmap::IndexSet;
use crate::ast::*;
use std::collections::HashSet;

#[derive(Debug)]
pub struct ProofCompressor<'a>{
    original_proof: &'a Proof,
    proof: Proof,       //remove pub
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
        let mut collected_nodes: (Vec<(usize, usize)>, Vec<bool>)  = self.collect_units();
        self.fix_broken_proof(self.current_root, &mut collected_nodes);
        self.reinsert_units(units_queue);
    }*/

    fn collect_units(&self) -> (Vec<(usize, usize)>, HashSet<usize>){
        let mut units_queue: Vec<(usize, usize)> = Vec::new();
        let mut marked: HashSet<usize> = HashSet::new();
        self.recursive_collect_units(self.current_root, &mut marked, &mut units_queue);
        let mut deleted: HashSet<usize> = HashSet::new();
        for (i,j) in &units_queue{
            if j>&1 {               //the if ensures the node has more than one child
                deleted.insert(*i);
                ()
            }
        }
        (units_queue, deleted)
    }

    fn recursive_collect_units(
        &self, node: usize, 
        marked: &mut HashSet<usize>, 
        units_queue: &mut Vec<(usize, usize)>
    ) -> (){
        match &self.proof.commands[node]{
            ProofCommand::Assume{..} => {
                //This node will always be unary, because if it wasn't unary, the next step of the proof
                //would have to be derived through the "or" rule, and if it was derived through the or rule,
                //this function wouldn't be recursivelly called for this node
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
                if ps.rule!="or"{
                    for (_,i) in &ps.premises{
                        self.recursive_collect_units(*i, marked, units_queue);
                    }
                }
                marked.remove(&node);
            }
        }
    }

    fn fix_broken_proof(&mut self, node:usize, collected_nodes: &mut (Vec<(usize, usize)>, Vec<bool>))-> (){
        let mut deleted: &Vec<bool> = &collected_nodes.1;
        let units_queue: &Vec<(usize, usize)> = &collected_nodes.0;
        match &self.proof.commands[node]{
            ProofCommand::Assume{..} => (),
            ProofCommand::Subproof(_) => (),
            ProofCommand::ProofStep(ps) => {
                for (_,i) in &ps.premises{
                    if deleted[*i]{

                    }
                }
            }
        }
    }

}


    