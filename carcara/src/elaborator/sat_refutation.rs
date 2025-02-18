use super::*;
use crate::external::*;
use std::collections::HashMap;
use std::fs;
use std::{
    fs::File,
    io::{BufRead, Write},
    process::{Command, Stdio},
};

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

fn get_resolution_refutation(
    pool: &mut PrimitivePool,
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

    let var_to_term: HashMap<i32, &Rc<Term>> =
        term_to_var.iter().map(|(k, v)| (v.clone(), k.clone())).collect();
    let mut id = 0;
    let mut clause_id_to_proof: HashMap<usize, Rc<ProofNode>> = fs::read_to_string(cnf_path)
        .unwrap()
        .lines()
        .skip(1)
        .map(|l| {
            id += 1;
            let sat_clause_lits : Vec<Rc<Term>> = String::from(l)
                .split(" ")
                .filter_map(|lit| match lit.parse::<i32>() {
                    Ok(lit) if lit != 0 => {
                        let (pol, var) = get_pol_var(lit);
                        let term = var_to_term[&var].clone();
                        Some(if pol { term } else { build_term!(pool, (not {term})) })
                    },
                    _ => None,
                })
                .collect();
            let term = pool.add(Term::Op(Operator::RareList, sat_clause_lits.clone()));
            (id, Rc::new(ProofNode::Assume { id: format!("a{}", id), depth: 0, term}))
        })
        .collect();

    println!("Input {:?}", clause_id_to_proof);

    // let lines = fs::read_to_string("proof.lrat")
    //     .unwrap()
    //     .lines()
    //     .skip(1)
    //     .map(|l| {l.unwrap()}).collect();

    let res_steps: Vec<(Vec<Rc<Term>>, Vec<usize>)> = fs::read_to_string("proof.lrat")
        .unwrap()
        .lines()
        .rev()
        .filter_map(|l| {
            let string = String::from(l);
            let strings : Vec<&str> = string.split(" ").collect();
            if strings[1] == "d" {
                return None;
            }
            let mut i = 1;
            let mut sat_clause_lits : Vec<Rc<Term>> = Vec::new();
            // parse clause
            println!("String {:?}", strings);
            loop {
                let sat_lit = strings[i].parse::<i32>().unwrap();
                if sat_lit == 0 {
                    break;
                }
                let (pol, var) = get_pol_var(sat_lit);
                let term = var_to_term[&var].clone();
                let lit = if pol { term } else { build_term!(pool, (not {term})) };
                sat_clause_lits.push(lit);
                i += 1;
            }
            // parse premises
            let premises : Vec<usize> = strings.iter().skip(i)
                .filter_map(|premise| match premise.parse::<usize>() {
                    Ok(premise) if premise != 0 => Some(premise),
                    _ => None,
                })
                .collect();
            Some((sat_clause_lits, premises))
        })
        .collect();

    println!("Res steps: {:?}", res_steps);

    Ok(Rc::new(ProofNode::Assume {
        id: "".to_string(),
        depth: 0,
        term: pool.bool_constant(true),
    }))
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
        // let res_refutation = get_resolution_refutation(elaborator.pool, cnf_path, &term_to_var);

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
