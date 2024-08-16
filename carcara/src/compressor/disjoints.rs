use super::ProofCommand;
use crate::ast::proof::*;
use crate::ast::rc::Rc;
use crate::ast::term::Term;
use indexmap::IndexSet;

#[derive(Debug)]
pub struct DisjointPart{
    pub part_commands: Vec<PartStep>,
    pub units_queue: IndexSet<(usize,usize)>,
    pub compressible: bool,
}

#[derive(Debug)]
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
    pub fn new(is_resolution: bool) -> Self{
        Self{
            part_commands: vec![],
            units_queue: IndexSet::new(),
            compressible: is_resolution,
            
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