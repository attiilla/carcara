use super::ProofCommand;
use crate::ast::proof::*;
use crate::ast::rc::Rc;
use crate::ast::term::Term;
use indexmap::IndexSet;
use std::collections::{HashSet, HashMap};
use std::fmt;


pub struct DisjointPart{
    pub part_commands: Vec<PartStep>,
    pub units_queue: IndexSet<(usize, usize)>,
    pub marked_for_deletion: IndexSet<(usize, usize)>,
    pub compressible: bool,
    pub ind: usize,
    pub depth: usize,
}


pub struct PartStep{
    pub ind: usize,
    pub proof_ind: Option<(usize,usize)>,
    pub premises: Vec<(usize,usize)>, //steps that appear explicitly on premises
    pub indirect_premises: Vec<(usize,usize)>,
    pub local_premises: Vec<usize>,
    pub rule: String,
    pub clause: Vec<Rc<Term>>,
    pub args: Vec<ProofArg>

}

impl DisjointPart{
    pub fn new(is_resolution: bool, ind: usize, depth: usize) -> Self{
        Self{
            part_commands: vec![],
            units_queue: IndexSet::new(),
            marked_for_deletion: IndexSet::new(),
            compressible: is_resolution,
            ind,
            depth,
        }
    }

    pub fn conclusion(&self) -> &Vec<Rc<Term>>{
        match self.part_commands.get(0){
            None => panic!("This part is empty"),
            Some(ps) => &ps.clause
        }
    }

    pub fn all_premises_remain(&self, clause: &PartStep) -> bool{
        clause.premises.iter().fold(true, |acc, prem| acc && !self.removed(prem))
    }

    pub fn some_premises_remains(&self, clause: &PartStep) -> bool{
        let remain: usize = clause.premises.iter().fold(0, |acc, prem| if !self.removed(prem) { acc+1 } else {acc});
        (remain != clause.premises.len()) && (remain != 1) 
    }

    pub fn single_premise_remains(&self, clause: &PartStep) -> bool{
        let remain: usize = clause.premises.iter().fold(0, |acc, prem| if !self.removed(prem) { acc+1 } else {acc});
        (remain != clause.premises.len()) && (remain == 1) 
    }

    pub fn remaining_premises(&self, clause: &PartStep) -> Vec<(usize, usize)> {
        //clause.premises.iter().fold(Vec::new(), |acc, &prem| if !self.removed(&prem) { acc.push(prem) } else {})
        let ans: Vec<_> = clause.premises.iter().filter(|&prem| !self.removed(prem)).cloned().collect();
        ans
    }

    fn removed(&self, step: &(usize, usize)) -> bool{
        self.units_queue.contains(step) || self.marked_for_deletion.contains(step)
    }

    pub fn substitute(&mut self, table: &mut HashMap<(usize,usize),(usize,usize)>, index: (usize, usize), trgt_index: (usize, usize)){
        if let Some(end_index) = table.get(&trgt_index){
            table.insert(index,*end_index);
        } else {
            table.insert(index,trgt_index);
        }
        self.marked_for_deletion.insert(index);
    }

}

impl PartStep{
    pub fn new(
        ind: usize, 
        proof_ind: Option<(usize,usize)>,
        premises: Vec<(usize,usize)>,
        indirect_premises: Vec<(usize,usize)>,
        rule: String,
        clause: Vec<Rc<Term>>,
        args: Vec<ProofArg>,
    )->Self{
        Self{
            ind,
            proof_ind,
            premises,
            indirect_premises,
            local_premises: vec![],
            rule,
            clause,
            args,
        }
    }
}

impl fmt::Debug for DisjointPart {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f,"Part {:?}.{:?}", self.depth, self.ind)?;
        for com in self.part_commands.iter(){
            write!(f,"{:?}",com)?;
        }
        Ok(())
    }
}

impl fmt::Debug for PartStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"ind {:?}, proof_ind {:?}",self.ind,self.proof_ind)?;
        write!(f,"; rule: {:?}; args: {:?}", &self.rule, &self.args)?;
        write!(f,"; clause: {:?}",&self.clause)?;
        if self.premises.len()>0{
            write!(f, "; premises: {:?}",&self.premises)?;
            if self.local_premises.len()>0{
                write!(f, "; local premises: {:?}",&self.local_premises)?;
            }else{
                write!(f, "; The local premises weren't computed yet or all premises from this clause are not in this part")?;
            }
        }
        if self.indirect_premises.len()>0{
            write!(f,"; indirect premises: {:?}",&self.indirect_premises)?;
        }
        println!("\n");
        Ok(())
    }
}