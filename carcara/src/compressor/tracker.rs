use std::collections::{HashSet, HashMap};
use super::error::*;
use super::disjoints::*;
//use super::Proof;
use crate::ast::proof::*;
use crate::ast::rc::Rc;
use crate::ast::term::Term;
//use crate::compressor::error::*;
//use crate::compressor::dsjoints::*;
//stores the information from the clause (i,j) across distinct parts
#[derive(Debug)]
pub(super) struct PartTracker{
    track_data: HashMap<(usize,usize), TrackerData>,
    parts: Vec<DisjointPart>
}

#[derive(Debug)]
struct TrackerData{
    parts_belonged: HashSet<usize>, //the parts (i, j) belong to
    part_count: HashMap<usize, usize>, //stores the number of times (i,j) appears on the part key
    pub inv_index: HashMap<usize, usize>, //the index of (i,j) in the part key
    global_index: (usize, usize) //the (i, j)
}

impl PartTracker{
    pub fn new() -> Self{
        let mut parts: Vec<DisjointPart> = Vec::new();
        parts.push(DisjointPart::new()); //the part 0 must contain all the assumes
        parts.push(DisjointPart::new()); //the part 1 must contain the conclusion
        Self{
            track_data: HashMap::new(),
            parts,
        }
    }

    pub fn add_step_to_part(&mut self, step: (usize, usize), part_ind: usize){//OK
        match self.track_data.get_mut(&step){
            Some(tracker) => { // The step is already in some part
                tracker.add_one_more_to_part(part_ind);
            }
            None => { // The step is new
                let tracker = TrackerData::new(step, part_ind, None);
                self.track_data.insert(step,tracker);
            }
        }
    }

    pub fn set_index_in_part(&mut self, step: (usize, usize), ind: usize, part_ind: usize){//OK
        match self.track_data.get_mut(&step){
            Some(tracker) => tracker.inv_index.insert(part_ind,ind),
            None => panic!("Unexpected behavior\nYou can't set the index of a clause that is not being tracked")
        };
    }

    pub fn parts_containing(&self, step: (usize, usize)) -> Result<Vec<usize>,CollectionError>{//OK
        match self.track_data.get(&step){
            Some(tracker) => Ok(tracker.parts_belonged_ref().iter().cloned().collect()),
            None => Err(CollectionError::NodeWithoutInwardEdge)
        }
    }

    pub fn add_step_to_new_part(&mut self, step: (usize, usize)) -> usize{//OK
        let new_part_ind: usize = self.parts.len();
        self.parts.push(DisjointPart::new());
        self.add_step_to_part(step, new_part_ind);
        new_part_ind
    }

    pub fn clone_data_to_part(&mut self, step: (usize, usize), part_ind: usize, commands: &Vec<ProofCommand>){//OK
        let mut part_commands: &mut Vec<PartStep> = &mut self.parts[part_ind].part_commands;
        let ind = part_commands.len();
        let premises: Vec<(usize,usize)>;
        let rule: String;
        let clause: Vec<Rc<Term>>;
        let args: Vec<ProofArg>;
        match commands.get(step.1){
            Some(ProofCommand::Assume { id, term })=> {
                premises = vec![];
                rule = "Assume".to_string();
                clause = vec![Rc::clone(term)];
                args = vec![];
            }
            Some(ProofCommand::Step(ps)) => {
                premises = ps.premises.clone();
                rule = ps.rule.clone();
                clause = ps.clause.clone();
                args = ps.args.clone();
            }
            Some(ProofCommand::Subproof(sp)) => {
                match sp.commands.last(){
                    Some(ProofCommand::Step(sub_ps)) => {
                        premises = sub_ps.premises.clone();
                        rule = sub_ps.rule.clone();
                        clause = sub_ps.clause.clone();
                        args = sub_ps.args.clone();
                    }
                    Some(_) => panic!("The last step of a subproof should be a ProofStep."),
                    None => panic!("This subproof shouldn't be empty.")
                }
            }
            None => panic!("The part index is too large. Can't add data to a part that doesn't exist")
        }
        let part_step = PartStep::new(
            ind,
            Some(step),
            premises,
            rule,
            clause,
            args,
        );
        part_commands.push(part_step);
    }

    pub fn counting_in_part(&self, step: (usize, usize), part_ind: usize) -> usize{
        match self.track_data.get(&step){
            Some(tracker) => {
                match tracker.part_count.get(&part_ind){
                    Some(ans) => *ans,
                    None => panic!("This step seems to be inside this part but wasn't counted.")
                }
            },
            None => panic!("This step is not in this part")
        }
    }

    pub fn add_to_units_queue_of_part(&mut self, step: (usize,usize), part_ind: usize){
        match self.parts.get_mut(part_ind){
            Some(part) => {
                part.units_queue.insert(step);
            },
            None => panic!("Impossible adding to queue of a part that doesn't exist")
        }
    }
}

impl TrackerData{
    pub fn new(key: (usize, usize), first_part: usize, ind: Option<usize>) -> TrackerData{
        let parts_belonged: HashSet<usize> = std::iter::once(first_part).collect();
        let part_count: HashMap<usize, usize> = std::iter::once((first_part, 1)).collect();
        let inv_index: HashMap<usize, usize>;
        match ind{
            Some(k) => inv_index = std::iter::once((first_part, k)).collect(),
            None => inv_index = HashMap::new()
        };
        TrackerData{
            parts_belonged,
            part_count,
            inv_index,
            global_index: key
        }
    }

    pub fn add_one_more_to_part(&mut self, numb: usize){
        if self.parts_belonged.contains(&numb){ // step already seen in this part
            if let Some(c) = self.part_count.get_mut(&numb) {
                *c += 1;
            } else {
                panic!("Some clause was added to a part but wasn't counted as such");
            }
        } else { // step is new in this part
            self.parts_belonged.insert(numb);
            self.part_count.insert(numb,1);
        }
    }

    pub fn parts_belonged_ref(&self) -> &HashSet<usize>{
        &self.parts_belonged
    }
}