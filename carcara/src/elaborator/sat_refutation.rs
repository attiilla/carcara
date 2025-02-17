use super::*;
use crate::checker::error::LiaGenericError;
use crate::external::*;
use std::collections::HashMap;
use std::process;
use std::{
    fs::File,
    io::Write,
    process::{Command, Stdio},
};

fn get_premise_steps(premise_nodes: &Vec<Rc<ProofNode>>) -> Vec<ProofCommand> {
    let mut commands: Vec<&ProofCommand> = Vec::new();

    commands
}

pub fn sat_refutation(elaborator: &mut Elaborator, step: &StepNode) -> Option<Rc<ProofNode>> {
    // TODO get commands out of step children. See proof_node_to_list
    let premise_steps = get_premise_steps(&step.premises);

    let mut lemmas: Vec<Rc<Term>> = Vec::new();
    let mut clause_id_to_lemma: HashMap<usize, Rc<Term>> = HashMap::new();
    let premise_clauses =
        collect_premise_clauses(elaborator.pool, &premise_steps, &mut lemmas, &mut clause_id_to_lemma);

    let mut sat_clause_to_lemma: HashMap<Vec<i32>, Rc<Term>> = HashMap::new();
    let cnf_path = gen_dimacs(
        &premise_clauses,
        &clause_id_to_lemma,
        &mut sat_clause_to_lemma,
        false,
    );
    if let Ok(core_lemmas) = get_core_lemmas(cnf_path, &sat_clause_to_lemma) {
        // for each core lemma, we will run cvc5, parse the proof in, and check it
        for i in 0..core_lemmas.len() {
            // println!("\tCheck lemma {:?}", lemma);
            let problem = get_problem_string(elaborator.pool, &elaborator.problem.prelude.clone(), &core_lemmas[i][..]);

            let commands = match get_solver_proof(elaborator.pool, problem.clone()) {
                Ok((c, _)) => c,
                Err(e) => {
                    log::warn!("failed to elaborate theory lemma {:?}: {}", core_lemmas[i], e);
                    return None;
                }
            };
            // TODO insert solver proof
        }
    }
    None
}
