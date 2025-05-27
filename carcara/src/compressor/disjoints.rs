use super::{ProofCommand, SubproofMeta};
use crate::ast::proof::*;
use crate::ast::term::Term;
use crate::ast::rc::Rc;
use indexmap::IndexSet;
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct DisjointPart {
    pub part_commands: Vec<ProofCommand>,
    pub original_index: Vec<(usize, usize)>,
    pub units_queue: IndexSet<(usize, usize)>,
    pub queue_local: IndexSet<usize>,
    pub args_queue: IndexSet<(Rc<Term>, Rc<Term>)>,
    pub marked_for_deletion: IndexSet<(usize, usize)>,
    pub compressible: bool,
    pub compressed: bool,
    pub ind: usize,
    pub subs_table: HashMap<(usize, usize), (usize, usize)>,
    pub inv_ind: HashMap<(usize, usize), usize>,
    pub behaved_steps: IndexSet<(usize, usize)>,
    pub recomputed: HashSet<(usize,usize)>,
}

impl ProofCommand {
    pub fn premises_old<'a>(
        &'a self,
        sp_stack: &'a Vec<SubproofMeta>,
    ) -> Option<&'a Vec<(usize, usize)>> {
        // ok
        match &self {
            ProofCommand::Assume { .. } => None,
            ProofCommand::Step(ps) => Some(&ps.premises),
            ProofCommand::Subproof(ssp) => {
                let sp = &sp_stack[ssp.context_id].proof;
                match sp.commands.last() {
                    Some(pc) => match pc {
                        ProofCommand::Step(ps) => Some(&ps.premises),
                        _ => panic!("The last command of a subproof should be a step"),
                    },
                    None => {
                        panic!("An empty subproof doesn't concludes anything. This proof is wrong")
                    }
                }
            }
        }
    }
}

impl<'a> DisjointPart {
    pub fn new(is_resolution: bool, ind: usize) -> Self {
        Self {
            part_commands: vec![],
            original_index: vec![],
            units_queue: IndexSet::new(),
            args_queue: IndexSet::new(),
            queue_local: IndexSet::new(),
            marked_for_deletion: IndexSet::new(),
            compressible: is_resolution,
            compressed: false,
            ind,
            subs_table: HashMap::new(),
            inv_ind: HashMap::new(),
            behaved_steps: IndexSet::new(),
            recomputed: HashSet::new()
        }
    }

    pub fn all_premises_remain(
        &self,
        command: &ProofCommand,
    ) -> bool {
        //ok
        let premises = command.premises();
        premises.iter().all(|prem| !self.marked_to_removal(prem))
        
    }

    pub fn some_premises_remains(
        &self,
        command: &ProofCommand,
    ) -> bool {
        //ok
        let premises = command.premises();
        let remain: usize = premises.iter().fold(0, |acc, prem| {
                if self.marked_to_removal(prem) {
                    acc
                } else {
                    acc + 1
                }
            });
        (remain != premises.len()) && (remain > 1)
    }

    pub fn single_premise_remains(
        &self,
        command: &ProofCommand,
    ) -> bool {
        //ok
        let premises = command.premises();
        let remain: usize = premises.iter().fold(0, |acc, prem| {
            if self.marked_to_removal(prem) {
                acc
            } else {
                acc + 1
            }
        });
        (remain != premises.len()) && (remain == 1)
    }

    pub fn remaining_premises(
        &self,
        ind: usize,
    ) -> Vec<(usize, usize)> {
        //ok
        let command = &self.part_commands[ind];
        let premises = command.premises(); 
        let ans: Vec<_> = premises
                .iter()
                .filter(|&prem| !self.marked_to_removal(prem))
                .copied()
                .collect();
        ans
    }

    pub fn some_premises_changed(
        &self,
        command: &ProofCommand,
        modified: &mut HashSet<(usize, usize)>,
    ) -> bool {
        //ok
        let premises = command.premises();
        premises.iter().any(|prem| modified.contains(prem))
    }

    pub fn marked_to_removal(&self, step: &(usize, usize)) -> bool {
        //ok
        self.units_queue.contains(step)
    }

    pub fn substitute(&mut self, index: (usize, usize), trgt_index: (usize, usize)) {
        // ok
        let table = &mut self.subs_table;
        if let Some(&end_index) = table.get(&trgt_index) {
            table.insert(index, end_index);
        } else {
            table.insert(index, trgt_index);
        }
        self.marked_for_deletion.insert(index);
    }

    pub fn substituted_by(&self, subs_index: (usize, usize)) -> Option<&(usize, usize)> {
        self.subs_table.get(&subs_index)
    }

    pub fn is_behaved(&self, local_index: usize) -> bool {
        //ok
        match &self.original_index.get(local_index) {
            Some(&global_index) => self.behaved_steps.contains(&global_index),
            None => panic!("Index out of bounds. The part is smaller than the index"),
        }
    }

    pub fn get_substitute(
        &'a self,
        substituted: &'a ProofCommand,
        old_index: (usize, usize),
    ) -> (&'a ProofCommand,(usize, usize)) {
        match self.subs_table.get(&old_index) {
            None => (substituted,old_index),
            Some(substitute_ind) => {
                let position = *self.inv_ind.get(substitute_ind).unwrap_or_else(|| {
                    panic!("The step {:?} is not in the inverted index", substitute_ind)
                });
                (&self.part_commands[position],*substitute_ind)
            }
        }
    }

    pub fn local_index_of(&self, index: (usize, usize)) -> usize{
        *self.inv_ind.get(&index).unwrap_or_else(|| {
            panic!("The step {:?} is not in the inverted index", index)
        })
    }

    /*pub fn inverse_index(&self) -> &HashMap<(usize,usize), usize>{
        &self.inv_ind
    }*/

    pub fn must_be_recomputed(&self, command: &ProofCommand, modified: &mut HashSet<(usize,usize)>) -> bool {
        (self.all_premises_remain(command) && self.some_premises_changed(command, modified)) ||
        (self.some_premises_remains(command) && command.is_resolution())
    }

    pub fn must_be_substituted(&self, command: &ProofCommand) -> bool {
        self.single_premise_remains(command) && command.is_resolution()
    }

    pub fn set_recomputed(&mut self, index: (usize, usize)){
        self.recomputed.insert(index);
    }

    pub fn is_recomputed(&self, index: (usize, usize)) -> bool {
        self.recomputed.contains(&index)
    }
}
