use std::collections::{HashMap, HashSet};

use super::disjoints::*;
use super::error::*;
use super::SubproofMeta;
//use super::Proof;
use crate::ast::pool::PrimitivePool;
use crate::ast::proof::*;
use crate::ast::TermPool;
//use crate::compressor::error::*;
//use crate::compressor::dsjoints::*;
//stores the information from the clause (i,j) across distinct parts
#[derive(Debug)]
pub(super) struct PartTracker {
    track_data: HashMap<(usize, usize), TrackerData>,
    pub parts: Vec<DisjointPart>,
    resolutions_premises: HashSet<(usize, usize)>,
    next_part: usize,
    pub is_conclusion: HashSet<(usize, usize)>,
}

#[derive(Debug)]
struct TrackerData {
    parts_belonged: HashSet<usize>,    //the parts (i, j) belong to
    part_count: HashMap<usize, usize>, // HashMap<key,val> that stores the number of times val the command (i,j) appears on the part key
}

impl PartTracker {
    pub fn new(end_in_resolution: bool) -> Self {
        //okp
        let mut parts: Vec<DisjointPart> = Vec::new();
        parts.push(DisjointPart::new(false, 0)); //the part 0 must contain all the assumes
        parts.push(DisjointPart::new(end_in_resolution, 1)); //the part 1 must contain the conclusion
        Self {
            track_data: HashMap::new(),
            parts,
            resolutions_premises: HashSet::new(),
            next_part: 2,
            is_conclusion: HashSet::new(),
        }
    }

    pub fn must_collect_assume(&self, index: (usize,usize), part_ind: usize) -> bool{
        let req = 
            if self.is_premise_of_part_conclusion(index, part_ind) {3} 
            else {2};
        self.counting_in_part(index, part_ind)>=req &&
        self.is_resolution_part(part_ind)
    }

    pub fn must_be_collected(&self, index: (usize, usize), part_ind: usize, command: &ProofCommand) -> bool{
        let req = 
            if self.is_premise_of_part_conclusion(index, part_ind) {3} 
            else {2};
        self.counting_in_part(index, part_ind)>=req && command.clause().len()==1
    }

    pub fn get_containing_parts(&mut self, ind: (usize, usize), is_resolution_or_pseudo: bool) -> Vec<usize>{
        let containing: Vec<usize> = 
        match self.parts_containing(ind)
            {
                Ok(v) => v,
                Err(CollectionError::NodeWithoutInwardEdge) => {
                    let new_part_ind: usize = self.add_step_to_new_part(ind,is_resolution_or_pseudo);
                    vec![new_part_ind]
                }
                Err(_) => panic!("Unexpected error"),
            };
        containing
    }
    

    pub fn set_is_conclusion(&mut self, step: (usize, usize)) {
        //ok
        self.is_conclusion.insert(step);
    }

    pub fn mark_for_part(&mut self, step: (usize, usize), part_ind: usize) {
        //ok
        match self.track_data.get_mut(&step) {
            // The step is already in some part
            Some(tracker) => {
                tracker.add_one_more_to_part(part_ind);
            }
            None => {
                // The step is new
                let tracker = TrackerData::new(part_ind, None);
                self.track_data.insert(step, tracker);
            }
        }
    }

    pub fn add_step_to_new_part(&mut self, step: (usize, usize), is_resolution: bool) -> usize {
        //ok
        let new_part_ind: usize = self.parts.len();
        self.parts
            .push(DisjointPart::new(is_resolution, self.next_part));
        self.next_part += 1;
        self.mark_for_part(step, new_part_ind);
        self.set_is_conclusion(step);
        new_part_ind
    }

    pub fn parts_containing(&self, step: (usize, usize)) -> Result<Vec<usize>, CollectionError> {
        //ok
        match self.track_data.get(&step) {
            Some(tracker) => Ok(tracker.parts_belonged.iter().copied().collect()),
            None => Err(CollectionError::NodeWithoutInwardEdge),
        }
    }

    pub fn insert_to_part_old(
        &mut self,
        step: (usize, usize),
        part_ind: usize,
        commands: &[ProofCommand],
    ) {
        //ok
        let command_cloned: ProofCommand = match commands.get(step.1) {
            Some(p) => p.clone(),
            None => panic!("The index is out of bounds."),
        };
        let n = self.parts[part_ind].part_commands.len();
        self.parts[part_ind].part_commands.push(command_cloned);
        self.parts[part_ind].original_index.push(step);
        self.parts[part_ind].inv_ind.insert(step, n);
        //self.update_inv_index(step, part_ind, n);
    }

    pub fn insert_to_part(
        &mut self,
        step: (usize, usize),
        part_ind: usize,
        command: &ProofCommand,
    ) {
        //ok
        let command_cloned: ProofCommand = command.clone();
        let n = self.parts[part_ind].part_commands.len();
        self.parts[part_ind].part_commands.push(command_cloned);
        self.parts[part_ind].original_index.push(step);
        self.parts[part_ind].inv_ind.insert(step, n);
    }
    
    pub fn is_premise_of_part_conclusion(&self, index: (usize,usize), part_ind: usize) -> bool{
        let part = &self.parts[part_ind];
        let premises = part.part_commands[0].premises();
        premises.contains(&index)
    }

    pub fn counting_in_part(&self, step: (usize, usize), part_ind: usize) -> usize {
        //ok
        match self.track_data.get(&step) {
            Some(tracker) => match tracker.part_count.get(&part_ind) {
                Some(ans) => *ans,
                None => panic!("This step seems to be inside this part but wasn't counted."),
            },
            None => panic!("This step {:?} is not being tracked", step),
        }
    }

    pub fn add_to_units_queue_of_part(
        &mut self,
        step: (usize, usize),
        part_ind: usize,
        position: usize,
        command: &ProofCommand,
        proof_pool: &mut PrimitivePool,
    ) {
        //ok
        match self.parts.get_mut(part_ind) {
            Some(part) => {
                let literal = command.clause()[0].clone();
                let (parity, atom) = literal.remove_all_negations();
                let bool_constant = if parity % 2 == 0 {
                    proof_pool.bool_false()
                } else {
                    proof_pool.bool_true()
                };
                let args = (atom.clone(), bool_constant);
                part.units_queue.insert(step);
                part.queue_local.insert(position);
                part.args_queue.insert(args);
            }
            None => panic!("Impossible adding to queue of a part that doesn't exist"),
        }
    }

    pub fn add_to_units_queue_of_part_old(
        &mut self,
        step: (usize, usize),
        part_ind: usize,
        position: usize,
        sp_stack: &Vec<SubproofMeta>,
        proof_pool: &mut PrimitivePool,
    ) {
        //ok
        match self.parts.get_mut(part_ind) {
            Some(part) => {
                let literal = match &part.part_commands[position] {
                    ProofCommand::Assume { term, .. } => term.clone(),
                    ProofCommand::Step(ps) => ps.clause[0].clone(),
                    ProofCommand::Subproof(ssp) => {
                        let sp = &sp_stack[ssp.context_id].proof;
                        match sp.commands.last() {
                            None => panic!("This subproof is empty"),
                            Some(pc) => match pc {
                                ProofCommand::Step(ps) => ps.clause[0].clone(),
                                _ => panic!("The last command of a subproof should be a step"),
                            },
                        }
                    }
                };
                let (parity, atom) = literal.remove_all_negations();
                let bool_constant = if parity % 2 == 0 {
                    proof_pool.bool_false()
                } else {
                    proof_pool.bool_true()
                };
                let args = (atom.clone(), bool_constant);
                part.units_queue.insert(step);
                part.queue_local.insert(position);
                part.args_queue.insert(args);
            }
            None => panic!("Impossible adding to queue of a part that doesn't exist"),
        }
    }

    pub fn set_resolutions_premise(&mut self, step: (usize, usize)) {
        //ok
        self.resolutions_premises.insert(step);
    }

    pub fn is_premise_of_resolution(&self, step: (usize, usize)) -> bool {
        //ok
        self.resolutions_premises.contains(&step)
    }
    

    pub fn is_resolution_part(&self, part_ind: usize) -> bool {
        //ok
        match self.parts.get(part_ind) {
            Some(dp) => dp.compressible,
            None => panic!("There is no part with such a high index"),
        }
    }

    pub fn resolution_parts(&self, step: (usize, usize)) -> Vec<usize> {
        let mut ans: Vec<usize> = Vec::new();
        for (i, p) in self.parts.iter().enumerate() {
            if p.compressible {
                ans.push(i);
            }
        }
        ans
    }

    pub fn non_resolution_parts(&self, step: (usize, usize)) -> Vec<usize> {
        //ok
        let mut ans: Vec<usize> = Vec::new();
        let mut containing: Vec<usize> = vec![];
        match self.parts_containing(step) {
            Ok(v) => containing = v,
            _ => (),
        };
        for &i in &containing {
            if !self.parts[i].compressible {
                ans.push(i);
            }
        }
        ans
    }

    pub fn set_as_behaved(&mut self, step: (usize, usize), part_ind: usize) {
        let part = &mut self.parts[part_ind];
        part.behaved_steps.insert(step);
    }
}

impl TrackerData {
    pub fn new(first_part: usize, ind: Option<usize>) -> TrackerData {
        //ok
        let parts_belonged: HashSet<usize> = std::iter::once(first_part).collect();
        let part_count: HashMap<usize, usize> = std::iter::once((first_part, 1)).collect();
        TrackerData { parts_belonged, part_count }
    }

    pub fn add_one_more_to_part(&mut self, part_ind: usize) {
        //ok
        if self.parts_belonged.contains(&part_ind) {
            // step already seen in this part
            if let Some(count) = self.part_count.get_mut(&part_ind) {
                *count += 1;
            } else {
                panic!("Some clause was added to a part but wasn't counted as such");
            }
        } else {
            // step is new in this part
            self.parts_belonged.insert(part_ind);
            self.part_count.insert(part_ind, 1);
        }
    }
}
