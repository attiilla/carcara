use super::*;
use crate::external::*;
pub use printer::print_proof;
use std::collections::HashMap;
use std::fs;
use std::process::{Command, Stdio};

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

fn build_res_step(
    clause_id: &usize,
    res_steps: &HashMap<usize, (Vec<Rc<Term>>, Vec<usize>)>,
    ids: &mut IdHelper,
    clause_id_to_proof: &mut HashMap<usize, Rc<ProofNode>>,
) -> Rc<ProofNode> {
    let res_step = &res_steps[&clause_id];
    let premises: Vec<Rc<ProofNode>> = res_step
        .1
        .iter()
        .map(|i| {
            if let Some(pf) = clause_id_to_proof.get(i) {
                pf.clone()
            } else {
                let pf = build_res_step(i, res_steps, ids, clause_id_to_proof);
                clause_id_to_proof.insert(i.clone(), pf.clone());
                pf.clone()
            }
        })
        .collect();
    Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: 0,
        clause: res_step.0.clone(),
        rule: "resolution".to_owned(),
        premises,
        ..Default::default()
    }))
}

fn get_resolution_refutation(
    pool: &mut PrimitivePool,
    step: &StepNode,
    premise_to_proof: &HashMap<Rc<Term>, Rc<ProofNode>>,
    cnf_path: String,
    term_to_var: &HashMap<&Rc<Term>, i32>,
) -> Result<Rc<ProofNode>, ExternalError> {
    // not gonna pass input via stdin because in that case
    // CaDiCaL gets confused with receiving the name of the
    // proof file as an argument. If we could get the proof in
    // stdout then there would be no need to write a CNF file nor a DRAT file
    let cadical_process = Command::new("/home/hbarbosa/carcara/wt-cvc5/cadical/build/cadical")
        .args([
            cnf_path.clone(),
            "proof.lrat".to_string(),
            "--no-binary".to_string(),
            "--lrat".to_string(),
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(ExternalError::FailedSpawnSolver)?;

    let output = cadical_process
        .wait_with_output()
        .map_err(ExternalError::FailedWaitForSolver)?;
    // CaDiCaL's exit code when successful is 10/20 (for
    // sat/unsat), so this will not lead to a successful
    // output according to Rust. So the test here directly
    // checks stdout to see if the problem is found unsat.
    if let Ok(stdout) = std::str::from_utf8(&output.stdout) {
        if !stdout.contains("s UNSATISFIABLE") {
            return Err(ExternalError::OutputNotUnsat);
        }
    } else {
        return Err(ExternalError::SolverGaveInvalidOutput);
    }

    let var_to_term: HashMap<i32, &Rc<Term>> = term_to_var
        .iter()
        .map(|(k, v)| (v.clone(), k.clone()))
        .collect();
    let mut id = 0;
    let mut ids = IdHelper::new(&step.id);
    println!("Premises to proofs: {:?}", premise_to_proof);
    let mut clause_id_to_proof: HashMap<usize, Rc<ProofNode>> = fs::read_to_string(cnf_path)
        .unwrap()
        .lines()
        .skip(1)
        .filter_map(|l| {
            id += 1;
            let sat_clause_lits: Vec<Rc<Term>> = String::from(l)
                .split(" ")
                .filter_map(|lit| match lit.parse::<i32>() {
                    Ok(lit) if lit != 0 => {
                        let (pol, var) = get_pol_var(lit);
                        let term = var_to_term[&var].clone();
                        Some(if pol {
                            term
                        } else {
                            build_term!(pool, (not { term }))
                        })
                    }
                    _ => None,
                })
                .collect();
            // We *must* find a proof for this clause in `premise_to_proof`. The
            // one detail are the singleton clauses that we may have
            // introduced. Also, the lemmas will be clauses in the SAT proof but
            // OR nodes. So we must search for both.
            match &sat_clause_lits[..] {
                [term] => {
                    let cl = pool.add(Term::Op(Operator::RareList, vec![term.clone()]));
                    Some((id, premise_to_proof[&cl].clone()))
                }
                _ => {
                    let cl = pool.add(Term::Op(Operator::RareList, sat_clause_lits.clone()));
                    if let Some(pf) = premise_to_proof.get(&cl) {
                        Some((id, pf.clone()))
                    } else {
                        // we will try to find a proof then for (rare-list (or
                        // ...)), and we will need to add an OR step between
                        // that premise and the resolution proof. If we do not
                        // find it, it means this is a lemma that does not show
                        // up in the core
                        let or = pool.add(Term::Op(Operator::Or, sat_clause_lits.clone()));
                        let or_cl = pool.add(Term::Op(Operator::RareList, vec![or.clone()]));
                        if let Some(pf) = premise_to_proof.get(&or_cl) {
                            Some((
                                id,
                                Rc::new(ProofNode::Step(StepNode {
                                    id: ids.next_id(),
                                    depth: 0,
                                    clause: sat_clause_lits.clone(),
                                    rule: "or".to_owned(),
                                    premises: vec![pf.clone()],
                                    ..Default::default()
                                })),
                            ))
                        } else {
                            None
                        }
                    }
                }
            }
            // (id, Rc::new(ProofNode::Assume { id: format!("a{}", id), depth: 0, term}))
        })
        .collect();

    // println!("Input {:?}", clause_id_to_proof);

    let mut empty_clause_id = 0;
    let res_steps: HashMap<usize, (Vec<Rc<Term>>, Vec<usize>)> = fs::read_to_string("proof.lrat")
        .unwrap()
        .lines()
        .rev()
        .filter_map(|l| {
            let string = String::from(l);
            let strings: Vec<&str> = string.split(" ").collect();
            let id = strings[0].parse::<usize>().unwrap();
            // ignore deletion
            if strings[1] == "d" {
                return None;
            }
            let mut i = 1;
            let mut sat_clause_lits: Vec<Rc<Term>> = Vec::new();
            // parse clause
            loop {
                let sat_lit = strings[i].parse::<i32>().unwrap();
                if sat_lit == 0 {
                    break;
                }
                let (pol, var) = get_pol_var(sat_lit);
                let term = var_to_term[&var].clone();
                let lit = if pol {
                    term
                } else {
                    build_term!(pool, (not { term }))
                };
                sat_clause_lits.push(lit);
                i += 1;
            }
            if sat_clause_lits.len() == 0 {
                empty_clause_id = id;
            }
            // parse premises
            let premises: Vec<usize> = strings
                .iter()
                .skip(i)
                .filter_map(|premise| match premise.parse::<usize>() {
                    Ok(premise) if premise != 0 => Some(premise),
                    _ => None,
                })
                .collect();
            Some((id, (sat_clause_lits, premises)))
        })
        .collect();

    println!("Res steps: {:?}", res_steps);

    Ok(build_res_step(
        &empty_clause_id,
        &res_steps,
        &mut ids,
        &mut clause_id_to_proof,
    ))
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
    let mut term_to_var: HashMap<&Rc<Term>, i32> = HashMap::new();
    let cnf_path = gen_dimacs(
        &premise_clauses,
        &clause_id_to_lemma,
        &mut sat_clause_to_lemma,
        &mut term_to_var,
        false,
    );
    if let Ok(core_lemmas) = get_core_lemmas(cnf_path.clone(), &sat_clause_to_lemma) {
        let mut step_id_to_lemma_proof: HashMap<String, Option<Rc<ProofNode>>> = lemmas_to_step_ids
            .iter()
            .map(|(_, id)| (id.clone(), None))
            .collect();

        // for each core lemma, we will run cvc5, parse the proof in, and check it
        for i in 0..core_lemmas.len() {
            // println!("\tCheck (to elab) lemma {:?}", core_lemmas[i]);
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
        let premise_to_proof: HashMap<Rc<Term>, Rc<ProofNode>> = step
            .premises
            .iter()
            .filter_map(|premise| {
                let id = premise.id();
                if !step_id_to_lemma_proof.contains_key(id) {
                    Some((
                        elaborator
                            .pool
                            .add(Term::Op(Operator::RareList, premise.clause().to_vec())),
                        premise.clone(),
                    ))
                } else if let Some(proof) = &step_id_to_lemma_proof[id] {
                    Some((
                        elaborator
                            .pool
                            .add(Term::Op(Operator::RareList, proof.clause().to_vec())),
                        proof.clone(),
                    ))
                } else {
                    None
                }
            })
            .collect();

        let res_refutation = get_resolution_refutation(
            elaborator.pool,
            step,
            &premise_to_proof,
            cnf_path,
            &term_to_var,
        )
        .ok()?;
        let test = Proof {
            constant_definitions: Vec::new(),
            commands: res_refutation.into_commands(),
        };
        let _ = print_proof(elaborator.pool, &elaborator.problem.prelude, &test, false);

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
