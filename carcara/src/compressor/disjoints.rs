use super::ProofCommand;
use crate::ast::proof::*;
use crate::ast::rc::Rc;
use crate::ast::term::Term;
use indexmap::IndexSet;
use std::fmt;


pub struct DisjointPart{
    pub part_commands: Vec<PartStep>,
    pub units_queue: IndexSet<(usize,usize)>,
    pub compressible: bool,
    pub ind: usize,
    pub depth: usize,
}


pub struct PartStep{
    ind: usize,
    proof_ind: Option<(usize,usize)>,
    premises: Vec<(usize,usize)>,
    indirect_premises: Vec<(usize,usize)>,
    local_premises: Vec<usize>,
    rule: String,
    clause: Vec<Rc<Term>>,
    args: Vec<ProofArg>

}

impl DisjointPart{
    pub fn new(is_resolution: bool, ind: usize, depth: usize) -> Self{
        Self{
            part_commands: vec![],
            units_queue: IndexSet::new(),
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
        write!(f,"Part {:?}.{:?}", self.depth, self.ind)?;
        for com in self.part_commands.iter(){
            write!(f,"{:?}",com)?;
        }
        Ok(())
    }
}

impl fmt::Debug for PartStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"ind {:?}, proof_ind {:?}",self.ind,self.proof_ind)?;
        write!(f,"rule: {:?}; args: {:?}", &self.rule, &self.args)?;
        write!(f,"{:?}",&self.clause)?;
        if self.premises.len()>0{
            write!(f, "premises: {:?}",&self.premises)?;
            if self.local_premises.len()>0{
                write!(f, "local premises: {:?}",&self.local_premises)?;
            }else{
                write!(f, "The local premises weren't computed yet or all premises from this clause are not in this part")?;
            }
        }
        if self.indirect_premises.len()>0{
            write!(f,"indirect premises: {:?}",&self.indirect_premises)?;
        }
        Ok(())
    }
}