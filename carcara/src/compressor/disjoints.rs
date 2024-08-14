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
    rule: String,
    clause: Vec<Rc<Term>>,
    args: Vec<ProofArg>

}

impl DisjointPart{
    pub fn new(is_resolution: bool) -> Self{
        Self{
            part_commands: vec![],
            units_queue: IndexSet::new(),
            compressible: is_resolution 
        }
    }
}

impl PartStep{
    pub fn new(
        ind: usize, 
        proof_ind: Option<(usize,usize)>,
        premises: Vec<(usize,usize)>,
        rule: String,
        clause: Vec<Rc<Term>>,
        args: Vec<ProofArg>,
    )->Self{
        Self{
            ind,
            proof_ind,
            premises,
            rule,
            clause,
            args,
        }
    }
}