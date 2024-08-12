mod tracker;
//mod error;
use crate::ast::proof::*;
use crate::ast::node::*;
use std::collections::{HashSet, HashMap};
use std::ops::Index;
use crate::checker::rules::Premise;
use crate::checker::rules::resolution::{apply_generic_resolution/*, unremove_all_negations*/};
use crate::checker::error::CheckerError;
use crate::ast::rc::Rc;
use indexmap::{IndexMap, IndexSet};
use std::env;
use tracker::*;


#[derive(Debug)]
pub struct ProofCompressor{
    pub proof: Proof,
    sp_binder: HashSet<&'static str>,
    sp_stack: Vec<Vec<AnchorArg>>
}

#[derive(Debug)]
pub struct DisjointPart{
    commands: Vec<PartSteps>,
    number: usize
}

#[derive(Debug)]
struct PartSteps{
    ind: usize,
    proof_ind: Option<(usize,usize)>,
    premises: Option<Vec<(usize,usize)>>,
    //term: Rc<Term>
}

impl DisjointPart{
    fn new(number: usize) -> DisjointPart{
        DisjointPart{
            commands: vec![],
            number
        }
    }
}


impl ProofCompressor{
    pub fn from(p: Proof)->ProofCompressor{
        ProofCompressor{
            proof: p,
            sp_binder: HashSet::from_iter(vec!["subproof","let","sko_ex","sko_forall","bind","onepoint"].into_iter()),
            sp_stack: vec![]
        }
    }

    pub fn compress_proof(&mut self) -> Proof{
        let empty = vec![];
        self.lower_units(empty);
        self.proof.clone()
    }

    fn lower_units(&mut self, sub_adrs: Vec<usize>) -> Result<(),()>{
        self.collect_units(&sub_adrs);
        //self.fix_broken_proof();
        //self.reinsert_units();
        //self.rebuild();
        Ok(())
    }

    fn collect_units(&mut self, sub_adrs: &Vec<usize>) -> (){
        let level: usize = sub_adrs.len();
        //get commands and put the data of the current subproof in stack if the current proof a a subproof
        let commands_table = self.get_commands(sub_adrs);
        let commands: &Vec<ProofCommand> = commands_table[level];
        let n = commands.len();
        let mut deduced_by_resolution: Vec<bool> = vec![false;n]; 
        let mut parts: Vec<DisjointPart> = vec![];
        parts.push(DisjointPart::new(0)); //the part 0 must contain all the assumes
        parts.push(DisjointPart::new(1)); //the part 1 must contain the conclusion
        for i in (0..n).rev(){
            match &commands[i]{
                ProofCommand::Assume{id, term} => {
                    println!("assume");
                }
                ProofCommand::Step(ps) => {
                    println!("proof step");
                }
                ProofCommand::Subproof(sp) => {
                    println!("subproof");
                }
            };
        }
        let mut pt = PartTracker::new();
        let dj = &DisjointPart{
            commands: vec![],
            number: 3
        };
        pt.add_step_to_part((1,2), dj);
        pt.add_step_to_part((1,2), dj);
        ()
    }

    fn get_commands(&mut self, sub_adrs: &Vec<usize>) -> Vec<&Vec<ProofCommand>>{
        let mut commands_table: Vec<&Vec<ProofCommand>> = vec![];
        let mut commands = &self.proof.commands;
        commands_table.push(commands);
        for i in 0..sub_adrs.len(){
            let ind = sub_adrs[i];
            if let ProofCommand::Subproof(sp) = &commands[ind]{
                commands_table.push(&sp.commands);
                if i == sub_adrs.len()-1{
                    self.sp_stack.push(sp.args.clone());
                }
            } else {
                panic!("Subproof addressing is wrong");
            }
        }
        commands_table
    }
}