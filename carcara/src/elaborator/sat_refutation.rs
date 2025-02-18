use super::*;
use crate::external::*;
use std::collections::HashMap;

fn proof_node_to_command(node: &Rc<ProofNode>) -> ProofCommand {
    match node.as_ref() {
        ProofNode::Assume { id, term, .. } => {
            ProofCommand::Assume { id: id.clone(), term: term.clone() }
        }
        ProofNode::Step(s) => ProofCommand::Step(ProofStep {
            id: s.id.clone(),
            clause: s.clause.clone(),
            rule: s.rule.clone(),
            premises: Vec::new(),
            args: s.args.clone(),
            discharge: Vec::new(),
        }),
        ProofNode::Subproof(s) => {
            // let mut curr_step = s.last_step;
            // while curr_step.is_subproof() {
            //     curr_step = curr_step.last_step;
            // }
            proof_node_to_command(&s.last_step)
        }
    }
}

pub fn sat_refutation(elaborator: &mut Elaborator, step: &StepNode) -> Option<Rc<ProofNode>> {
    // Get commands out of step children. See proof_node_to_list
    let mut commands: Vec<ProofCommand> = Vec::new();

    step.premises.iter().for_each(|premise| {
        commands.push(proof_node_to_command(premise));
    });
    let command_refs = commands.iter().map(|c| c).collect();

    let mut lemmas_to_step_ids: HashMap<Rc<Term>, String> = HashMap::new();
    let mut clause_id_to_lemma: HashMap<usize, Rc<Term>> = HashMap::new();
    let premise_clauses = collect_premise_clauses(
        elaborator.pool,
        &command_refs,
        &mut lemmas_to_step_ids,
        &mut clause_id_to_lemma,
    );

    let mut sat_clause_to_lemma: HashMap<Vec<i32>, Rc<Term>> = HashMap::new();
    let cnf_path = gen_dimacs(
        &premise_clauses,
        &clause_id_to_lemma,
        &mut sat_clause_to_lemma,
        false,
    );
    if let Ok(core_lemmas) = get_core_lemmas(cnf_path, &sat_clause_to_lemma) {
        let mut step_id_to_lemma_proof: HashMap<String, Option<Rc<ProofNode>>> = lemmas_to_step_ids
            .iter()
            .map(|(_, id)| (id.clone(), None))
            .collect();

        // for each core lemma, we will run cvc5, parse the proof in, and check it
        for i in 0..core_lemmas.len() {
            println!("\tCheck (to elab) lemma {:?}", core_lemmas[i]);
            let problem = get_problem_string(
                elaborator.pool,
                &elaborator.problem.prelude.clone(),
                &core_lemmas[i][..],
            );

            let solver_proof_commands = match get_solver_proof(elaborator.pool, problem.clone()) {
                Ok((c, _)) => c,
                Err(e) => {
                    log::warn!(
                        "failed to elaborate theory lemma {:?}: {}",
                        core_lemmas[i],
                        e
                    );
                    return None;
                }
            };
            let lemma = elaborator
                .pool
                .add(Term::Op(Operator::RareList, core_lemmas[i].clone()));
            let step_id = &lemmas_to_step_ids[&lemma];
            let proof_node = insert_solver_proof(
                elaborator.pool,
                solver_proof_commands,
                &core_lemmas[i],
                step_id,
                0,
            );
            // println!("\tGot proof {:?}", proof_node);
            // TODO insert solver proof
            step_id_to_lemma_proof.insert(step_id.clone(), Some(proof_node));
        }
        Some(Rc::new(ProofNode::Step(StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: step.rule.clone(),
            premises: step
                .premises
                .iter()
                .filter_map(|premise| {
                    let id = premise.id();
                    if !step_id_to_lemma_proof.contains_key(id) {
                        Some(premise.clone())
                    } else if let Some(proof) = &step_id_to_lemma_proof[id] {
                        Some(proof.clone())
                    } else {
                        None
                    }
                })
                .collect(),
            ..Default::default()
        })))
    } else {
        None
    }
}
