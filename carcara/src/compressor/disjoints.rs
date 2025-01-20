use super::{PartTracker, ProofCommand, ProofCompressor, SubproofMeta};
use crate::ast::proof::*;
use crate::ast::rc::Rc;
use crate::ast::term::Term;
use indexmap::IndexSet;
use std::collections::{HashSet, HashMap};
use std::fmt;

#[derive(Debug)]
pub struct DisjointPart{
    pub part_commands: Vec<ProofCommand>,
    pub original_index: Vec<(usize,usize)>,
    //pub part_root: Rc<ProofNode>,
    //pub indexes_vec: Vec<(usize, usize)>,
    //pub part_commands: Vec<PartStep>,
    pub units_queue: IndexSet<(usize, usize)>,
    pub queue_local: IndexSet<usize>,
    pub args_queue: IndexSet<(ProofArg, ProofArg)>,
    pub marked_for_deletion: IndexSet<(usize, usize)>,
    pub compressible: bool,
    pub compressed: bool,
    pub inverse_index: HashMap<(usize, usize),usize>,
    pub ind: usize,
    pub depth: usize,
    pub subs_table: HashMap<(usize,usize),(usize,usize)>,
    pub behaved_steps: IndexSet<(usize,usize)>,
    pub new_conclusion: Option<ProofCommand>,
}



/*pub struct PartStep{
    pub ind: usize,
    pub proof_ind: Option<(usize,usize)>,
    pub premises: Vec<(usize,usize)>, //steps that appear explicitly on premises
    pub indirect_premises: Vec<(usize,usize)>,
    //pub local_premises: Vec<usize>,
    pub rule: String,
    pub clause: Vec<Rc<Term>>,
    pub args: Vec<ProofArg>,
    pub anchor: Vec<AnchorArg>,
    pub context_id: Option<usize>,
    pub sub: bool,
    pub discharge: Vec<(usize,usize)>,
}*/

/*pub enum PartStep{
    Assume(MAssume),
    Step(MStep),
    Subproof(SubproofPlaceholder)
}*/

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct OuterPremiseAdrs{
    index: (usize, usize),
    sp: Option<usize>
}

/*pub struct MAssume{
    id: String, 
    term: Vec<Rc<Term>>, 
    index: Option<(usize,usize)> 
}
impl MAssume{
    pub fn new(id: String, term: Rc<Term>, index: Option<(usize,usize)>) -> Self{
        Self{
            id,
            term: vec![term],
            index
        }
    }
}

pub struct MStep{
    step: ProofStep,
    index: Option<usize>,
}

pub struct SubproofPlaceholder{
    index: Option<usize>,
    global_adrs: usize,
    all_premises: Vec<OuterPremiseAdrs>,
    all_premises_were_computed: bool,
    step: ProofStep,
}

impl SubproofPlaceholder{
    pub fn new(global_adrs: usize, index: Option<usize>, sp: &Subproof) -> Self{
        let step = match sp.commands.last(){
            None => panic!("An empty subproof doesn't concludes anything. This proof is wrong"),
            Some(p) => match p{
                ProofCommand::Step(ps) => ps.clone(),
                _ => panic!("The last step of a subproof should be a proofstep"),
            }
        };
        Self {
            index,
            global_adrs, 
            all_premises: vec![],
            all_premises_were_computed: false,
            step
        }
    }
}*/

//subs PartStep.index
//deleted clause

impl ProofCommand{
    /*pub fn clause(&self) -> &Vec<Rc<Term>>{
        match &self{
            ProofCommand::Assume{term, ..} => {

            },
            ProofCommand::Step(ps) => &ps.clause,
            ProofCommand::Subproof(sp) => {
                match sp.commands.last(){
                    Some(pc) => {
                        match pc{
                            ProofCommand::Step(ps) => &ps.clause,
                            _ => panic!("The last command of a subproof should be a step")
                        }
                    }
                    None => panic!("An empty subproof doesn't concludes anything. This proof is wrong")
                }
            }
        }
    }*/

    pub fn premises<'a>(&'a self, sp_stack: &'a Vec<SubproofMeta>) -> Option<&'a Vec<(usize, usize)>>{ // ok
        match &self{
            ProofCommand::Assume{..}=> None,
            ProofCommand::Step(ps) => Some(&ps.premises),
            ProofCommand::Subproof(ssp) => {
                let sp = &sp_stack[ssp.context_id].proof;
                match sp.commands.last(){
                    Some(pc) => {
                        match pc{
                            ProofCommand::Step(ps) => Some(&ps.premises),
                            _ => panic!("The last command of a subproof should be a step")
                        }
                    }
                    None => panic!("An empty subproof doesn't concludes anything. This proof is wrong")
                }
            }
        }
    }
}

impl DisjointPart{
    pub fn new(is_resolution: bool, ind: usize, depth: usize) -> Self{
        Self{
            part_commands: vec![],
            original_index: vec![],
            units_queue: IndexSet::new(),
            args_queue: IndexSet::new(),
            queue_local: IndexSet::new(),
            marked_for_deletion: IndexSet::new(),
            compressible: is_resolution,
            compressed: false,
            inverse_index: HashMap::new(),
            ind,
            depth,
            subs_table: HashMap::new(),
            behaved_steps: IndexSet::new(),
            new_conclusion: None
        }
    }

    /*pub fn compute_local_premises(&mut self, sp_stack: &Vec<Subproof>){
        for com in self.part_commands.iter_mut(){
            match com{
                ProofCommand::Assume {..} => {},
                ProofCommand::Step(ps) => {
                    let mut local_premises: Vec<(usize,usize)> = Vec::new();
                    for prem in ps.premises.iter(){
                        if let Some(local_index) = self.inverse_index.get(prem){
                            local_premises.push((prem.0,*local_index));
                        } else {
                            panic!("Premise not found in the inverse index")
                        }
                    }
                    ps.premises = local_premises;
                }
                ProofCommand::Subproof(ssp) => {
                    let mut local_premises: Vec<(usize,usize)> = Vec::new();
                    let sp = &sp_stack[ssp.context_id];
                    match sp.commands.last(){
                        Some(pc) => {
                            match pc{
                                ProofCommand::Step(ps) => {
                                    for prem in ps.premises.iter(){
                                        if let Some(local_index) = self.inverse_index.get(prem){
                                            local_premises.push((prem.0,*local_index));
                                        } else {
                                            panic!("Premise not found in the inverse index")
                                        }
                                    }
                                }
                                _ => panic!("The last command of a subproof should be a step")
                            }
                        }
                        None => panic!("An empty subproof doesn't concludes anything. This proof is wrong")
                    }
                    ssp.commands.push(ProofCommand::Step(ProofStep{
                        id: String::from(""),
                        clause: vec![],
                        rule: String::from(""),
                        premises: local_premises,
                        args: vec![],
                        discharge: vec![]
                    }));
                }
            }
        }
    }*/

    pub fn all_premises_remain(&self, sp_stack: &Vec<SubproofMeta>, command: &ProofCommand) -> bool{ //ok
        match command.premises(sp_stack){
            None => true,
            Some(p) => p.iter().fold(true, |acc, prem| acc && !self.removed(prem))
        }
    }

    pub fn some_premises_remains(&self, sp_stack: &Vec<SubproofMeta>, command: &ProofCommand) -> bool{ //ok
        match command.premises(sp_stack){
            None => false,
            Some(p) => {
                let remain: usize = p.iter().fold(0, |acc, prem| if !self.removed(prem) { acc+1 } else {acc});
                (remain != p.len()) && (remain > 1)
            }
        }
    }

    pub fn single_premise_remains(&self, sp_stack: &Vec<SubproofMeta>, command: &ProofCommand) -> bool{ //ok
        match command.premises(sp_stack){
            None => false,
            Some(p) => {
                let remain: usize = p.iter().fold(0, |acc, prem| if !self.removed(prem) { acc+1 } else {acc});
                (remain != p.len()) && (remain == 1)
            }
        }
    }

    pub fn remaining_premises(&self, sp_stack: &Vec<SubproofMeta>, ind: usize) -> Vec<(usize, usize)> { //ok
        let command = &self.part_commands[ind];
        match command.premises(sp_stack){
            None => vec![],
            Some(p) => {
                let ans: Vec<_> = p.iter().filter(|&prem| !self.removed(prem)).cloned().collect();
                ans
            }
        }
    }

    pub fn some_premises_changed(&self, 
        sp_stack: &Vec<SubproofMeta>, 
        command: &ProofCommand, 
        changed: &mut HashSet<(usize,usize)>
    ) -> bool{ //ok
        match command.premises(sp_stack){
            None => false,
            Some(p) => p.iter().fold(false, |acc, premise| acc || changed.contains(premise))
        }
    }

    pub fn removed(&self, step: &(usize, usize)) -> bool{ //ok
        self.units_queue.contains(step)
    }

    pub fn substitute(&mut self, index: (usize, usize), trgt_index: (usize, usize)){ // ok
        let mut table = &mut self.subs_table;
        if let Some(&end_index) = table.get(&trgt_index){
            table.insert(index,end_index);
        } else {
            table.insert(index,trgt_index);
        }
        self.marked_for_deletion.insert(index);
    }

    pub fn is_behaved(&self, local_index: usize)->bool{ //ok
        match &self.original_index.get(local_index){
            Some(&global_index) => {
                self.behaved_steps.contains(&global_index)
            }
            None => panic!("Index out of bounds. The part is smaller than the index"),
        }
    }


    pub fn set_arg(&mut self, ind: usize, args: Vec<ProofArg>){
        match &mut self.part_commands[ind]{
            ProofCommand::Assume { .. } => panic!("Assumes don't have args"),
            ProofCommand::Step(ps) => ps.args= args,
            ProofCommand::Subproof(sp_ph) => panic!("You shouldn't change this from outside of the subproof"),
        }
    }


    pub fn set_premises(&mut self, ind: usize, premises: Vec<(usize,usize)>){
        match &mut self.part_commands[ind]{
            ProofCommand::Assume { .. } => panic!("Assumes don't have args"),
            ProofCommand::Step(ps) => ps.premises = premises,
            ProofCommand::Subproof(sp_ph) => panic!("You shouldn't change this from outside of the subproof"),
        }
    }
}

/*impl PartStep{
    pub fn new(
        ind: usize, 
        proof_ind: Option<(usize,usize)>,
        premises: Vec<(usize,usize)>,
        indirect_premises: Vec<(usize,usize)>,
        rule: String,
        clause: Vec<Rc<Term>>,
        args: Vec<ProofArg>,
        anchor: Vec<AnchorArg>,
        context_id: Option<usize>,
        sub: bool,
        discharge: Vec<(usize,usize)>
    )->Self{
        Self{
            ind,
            proof_ind,
            premises,
            indirect_premises,
            //local_premises: vec![],
            rule,
            clause,
            args,
            anchor,
            context_id,
            sub,
            discharge,
        }
    }
}*/



/*impl fmt::Debug for DisjointPart {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f,"Part {:?}.{:?}", self.depth, self.ind)?;
        for com in self.part_commands.iter(){
           print_command(com);
        }
        Ok(())
    }
}*/





/*impl fmt::Debug for PartStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"ind {:?}, proof_ind {:?}",self.ind,self.proof_ind)?;
        write!(f,"; rule: {:?}; args: {:?}", &self.rule, &self.args)?;
        write!(f,"; clause: {:?}",&self.clause)?;
        if self.premises.len()>0{
            write!(f, "; premises: {:?}",&self.premises)?;
        }
        if self.indirect_premises.len()>0{
            write!(f,"; indirect premises: {:?}",&self.indirect_premises)?;
        }
        println!("\n");
        Ok(())
    }
}*/

fn format_index(tp: Option<(usize,usize)>) -> String{
    match tp{
        Some(i) => format!("({},{})",i.0,i.1),
        None => String::from("None")
    }
}