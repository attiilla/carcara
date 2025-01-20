use std::collections::{HashSet, HashMap};

use super::error::*;
use super::disjoints::*;
use super::SubproofMeta;
//use super::Proof;
use crate::ast::proof::*;
use crate::ast::rc::Rc;
use crate::ast::term::Term;
use crate::ast::pool::PrimitivePool;
use crate::ast::TermPool;
//use crate::compressor::error::*;
//use crate::compressor::dsjoints::*;
//stores the information from the clause (i,j) across distinct parts
#[derive(Debug)]
pub(super) struct PartTracker{
    track_data: HashMap<(usize, usize), TrackerData>,
    pub parts: Vec<DisjointPart>,
    resolutions_premises: HashSet<(usize, usize)>,
    next_part: usize,
    depth: usize,
    //cant_be_deleted: HashSet<(usize, usize)>,
    pub is_conclusion: HashSet<(usize, usize)>,
}

#[derive(Debug)]
struct TrackerData{
    parts_belonged: HashSet<usize>, //the parts (i, j) belong to
    part_count: HashMap<usize, usize>, //stores the number of times (i,j) appears on the part key
    inv_index: HashMap<usize, usize>, //the index of (i,j) in the part that is the key
    global_index: (usize, usize), //the (i, j)
}

impl PartTracker{
    pub fn new(end_in_resolution: bool, depth: usize) -> Self{ //okp
        let mut parts: Vec<DisjointPart> = Vec::new();
        parts.push(DisjointPart::new(false, 0, depth)); //the part 0 must contain all the assumes
        parts.push(DisjointPart::new(end_in_resolution, 1, depth)); //the part 1 must contain the conclusion
        Self{
            track_data: HashMap::new(),
            parts,
            resolutions_premises: HashSet::new(),
            next_part: 2,
            depth,
            //cant_be_deleted: HashSet::new(),
            is_conclusion: HashSet::new(),
        }
    }

    pub fn print_all_parts(&self){
        for (i, p) in self.parts.iter().enumerate(){
            println!("{:?}\n", p);
        }
    }

    pub fn print_part(&self, ind: usize){
        println!("{:?}", &self.parts[ind]);
    }

    pub fn set_is_conclusion(&mut self, step: (usize,usize)){ //ok
        self.is_conclusion.insert(step);
    }

    /*pub fn set_cant_be_deleted(&mut self, step: (usize,usize)){
        self.cant_be_deleted.insert(step);
    }*/


    pub fn add_step_to_part(&mut self, step: (usize, usize), part_ind: usize){ //ok
        match self.track_data.get_mut(&step){
            // The step is already in some part 
            Some(tracker) => {
                tracker.add_one_more_to_part(part_ind);
            },
            None => { // The step is new
                let tracker = TrackerData::new(step, part_ind, None);
                self.track_data.insert(step,tracker);
            }
        }
    }

    pub fn set_index_in_part(&mut self, step: (usize, usize), ind: usize, part_ind: usize){
        match self.track_data.get_mut(&step){
            Some(tracker) => tracker.inv_index.insert(part_ind,ind),
            None => panic!("Unexpected behavior\nYou can't set the index of a clause that is not being tracked")
        };
    }

    pub fn parts_containing(&self, step: (usize, usize)) -> Result<Vec<usize>,CollectionError>{ //ok
        match self.track_data.get(&step){
            Some(tracker) => Ok(tracker.parts_belonged_ref().iter().cloned().collect()),
            None => Err(CollectionError::NodeWithoutInwardEdge)
        }
    }

    pub fn add_step_to_new_part(&mut self, step: (usize, usize), is_resolution: bool) -> usize{ //ok
        let new_part_ind: usize = self.parts.len();
        self.parts.push(DisjointPart::new(is_resolution, self.next_part, self.depth));
        self.next_part += 1;
        self.add_step_to_part(step, new_part_ind);
        self.set_is_conclusion(step);
        new_part_ind
    }

    pub fn clone_data_to_part(&mut self, step: (usize, usize), part_ind: usize, commands: &Vec<ProofCommand>){ //ok
        let command_cloned: ProofCommand;
        match commands.get(step.1){
            Some(p) => {
                command_cloned = p.clone();
            }
            None => panic!("The index is out of bounds.")
        }
        let n = self.parts[part_ind].part_commands.len();
        self.parts[part_ind].part_commands.push(command_cloned);
        self.parts[part_ind].original_index.push(step);
        self.update_inv_index(step, part_ind, n);
    }

    /*pub fn clone_data_to_part_old(&mut self, step: (usize, usize), part_ind: usize, commands: &Vec<ProofCommand>, subs: &Vec<Subproof>, sub_full_premises: Option<Vec<(usize,usize)>>){
        let premises: Vec<(usize,usize)>;
        let indirect_premises: Vec<(usize,usize)>;
        let local_premises: Vec<usize> = vec![];
        let rule: String;
        let clause: Vec<Rc<Term>>;
        let args: Vec<ProofArg>;
        let mut disc = vec![];
        let mut anchor = vec![];
        let mut context_id = None;
        let n;
        let mut sub = false;
        {
            let mut part_commands: &mut Vec<PartCommands> = &mut self.parts[part_ind].part_commands;
            let ind = part_commands.len();
            match commands.get(step.1){
                Some(ProofCommand::Assume { id, term })=> {
                    premises = vec![];
                    indirect_premises = vec![];
                    rule = "Assume".to_string();
                    clause = vec![Rc::clone(term)];
                    args = vec![];
                }
                Some(ProofCommand::Step(ps)) => {
                    premises = ps.premises.clone();
                    indirect_premises = vec![];
                    rule = ps.rule.clone();
                    clause = ps.clause.clone();
                    args = ps.args.clone();
                    disc = ps.discharge.clone();
                }
                Some(ProofCommand::Subproof(ph_sp)) => {
                    sub = true;
                    let ad = ph_sp.context_id;
                    let sp = &subs[ad];
                    context_id = Some(sp.context_id);
                    anchor = sp.args.clone();
                    match sub_full_premises{
                        Some(v) => indirect_premises = v,
                        None => panic!("All clauses used internally by this subproof that aren't from this subproof must be passed here.\n
                        You must pass an empty vector if the subproof uses no such clauses.")
                    }
                    match sp.commands.last(){
                        Some(ProofCommand::Step(sub_ps)) => {
                            premises = sub_ps.premises.clone();
                            rule = sub_ps.rule.clone();
                            clause = sub_ps.clause.clone();
                            args = sub_ps.args.clone();
                            disc = sub_ps.discharge.clone();
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
                indirect_premises,
                rule,
                clause,
                args,
                anchor,
                context_id,
                sub,
                disc
            );

            n = part_commands.len();
            part_commands.push(part_step);
        }
        self.update_inv_index(step, part_ind, n);
    }
*/
    fn update_inv_index(&mut self, step: (usize,usize), part_ind: usize, ind: usize){
        match &mut self.track_data.get_mut(&step){
            Some(a) => a.inv_index.insert(part_ind,ind),
            None => panic!("track_data doesn't have a {:?}",step)
        };
    }

    pub fn counting_in_part(&self, step: (usize, usize), part_ind: usize) -> usize{ //ok
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

    pub fn inverse_index(&self, step: &(usize,usize), part: &usize) -> usize{
        match self.track_data.get(step){
            Some(a) => match a.inv_index.get(part){
                Some(b) => *b,
                None => panic!("The inv_index of {:?} doesn't have {:?}",step,part)
            },
            None => panic!("track_data doesn't have a {:?}",step)
        }
    }


    pub fn add_to_units_queue_of_part(&mut self, step: (usize,usize), part_ind: usize, position: usize, sp_stack: &Vec<SubproofMeta>, proof_pool: &mut PrimitivePool){//ok
        match self.parts.get_mut(part_ind){
            Some(part) => {
                let literal = match &part.part_commands[position]{
                    ProofCommand::Assume{term,..} => term.clone(),
                    ProofCommand::Step(ps) => ps.clause[0].clone(),
                    ProofCommand::Subproof(ssp) => {
                        let sp = &sp_stack[ssp.context_id].proof;
                        match sp.commands.last(){
                            None => panic!("This subproof is empty"),
                            Some(pc) => match pc{
                                ProofCommand::Step(ps) => ps.clause[0].clone(),
                                _ => panic!("The last command of a subproof should be a step")
                            }
                        }
                    }
                };
                let (parity, atom) = literal.remove_all_negations();
                let bool_constant = if parity%2==0 {proof_pool.bool_false()} else {proof_pool.bool_true()};
                let args = (ProofArg::Term(atom.clone()),ProofArg::Term(bool_constant));
                part.units_queue.insert(step);
                part.queue_local.insert(position);
                part.args_queue.insert(args);
            }
            None => panic!("Impossible adding to queue of a part that doesn't exist")
        }
    }

    pub fn set_resolutions_premise(&mut self, step: (usize, usize)){ //ok
        self.resolutions_premises.insert(step);
    }

    pub fn is_premise_of_resolution(&self, step: (usize, usize)) -> bool{ //ok
        self.resolutions_premises.contains(&step)
    }

    pub fn is_resolution_part(&self, part_ind: usize) -> bool{ //ok
        match self.parts.get(part_ind){
            Some(dp) => dp.compressible,
            None => panic!("There is no part with such a high index")
        }
    }

    pub fn resolution_parts(&self, step: (usize, usize)) -> Vec<usize>{
        let mut ans: Vec<usize> = Vec::new();
        for (i,p) in self.parts.iter().enumerate(){
            if p.compressible{
                ans.push(i);
            }
        }
        ans
    }

    pub fn non_resolution_parts(&self, step: (usize, usize)) -> Vec<usize>{//ok
        let mut ans: Vec<usize> = Vec::new();
        let mut containing: Vec<usize> = vec![];
        match self.parts_containing(step){
            Ok(v) => containing = v,
            _ => (),
        };
        for &i in &containing{
            if !self.parts[i].compressible{
                ans.push(i);
            }
        }
        ans
    }

    pub fn depth(&self) -> usize{
        self.depth
    }

    pub fn set_as_behaved(&mut self, step: (usize, usize), part_ind: usize){
        let part = &mut self.parts[part_ind];
        part.behaved_steps.insert(step);
    }
}

impl TrackerData{
    pub fn new(key: (usize, usize), first_part: usize, ind: Option<usize>) -> TrackerData{ //ok
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
            global_index: key,
        }
    }

    pub fn add_one_more_to_part(&mut self, part_ind: usize){ //ok
        if self.parts_belonged.contains(&part_ind){ // step already seen in this part
            if let Some(count) = self.part_count.get_mut(&part_ind) {
                *count += 1;
            } else {
                panic!("Some clause was added to a part but wasn't counted as such");
            }
        } else { // step is new in this part
            self.parts_belonged.insert(part_ind);
            self.part_count.insert(part_ind,1);
        }
    }

    pub fn parts_belonged_ref(&self) -> &HashSet<usize>{
        &self.parts_belonged
    }
}

