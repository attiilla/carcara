use super::*;
use crate::checker::error::LiaGenericError;
use crate::{checker, parser, CarcaraResult};
use std::collections::HashMap;
use std::fs;
use std::process;
use std::{
    fs::File,
    io::{BufRead, Write},
    process::{Command, Stdio},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExternalError {
    #[error("couldn't check lemma: '{0}'")]
    LemmaNotChecked(Rc<Term>),
}


fn get_problem_string(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    conclusion: &[Rc<Term>],
) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    writeln!(&mut problem, "(set-option :produce-proofs true)").unwrap();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_lia_smt_instance(pool, prelude, &mut bytes, conclusion, false).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();

    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

fn parse_and_check_solver_proof(
    pool: &mut PrimitivePool,
    problem: &[u8],
    proof: &[u8],
) -> CarcaraResult<(Vec<ProofCommand>, bool)> {
    let config = parser::Config {
        apply_function_defs: false,
        expand_lets: true,
        allow_int_real_subtyping: true,
        strict: false,
        parse_hole_args: false,
    };

    let (problem, proof) = parser::parse_instance_with_pool(problem, proof, config, pool)?;

    let config = checker::Config::new();
    let res = checker::ProofChecker::new(pool, config).check(&problem, &proof)?;
    Ok((proof.commands, res))
}

fn get_solver_proof(
    pool: &mut PrimitivePool,
    problem: String,
) -> Result<(Vec<ProofCommand>, bool), LiaGenericError> {
    let mut process = Command::new("/home/hbarbosa/cvc5/wt-diff/prod/bin/cvc5")
        .arg("--proof-format=alethe".to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(problem.as_bytes())
        .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(LiaGenericError::SolverTimeout);
            }
        }
        return Err(LiaGenericError::NonZeroExitCode(output.status.code()));
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| LiaGenericError::SolverGaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(LiaGenericError::OutputNotUnsat);
    }

    // println!("{}", problem);
    // println!("{}", std::str::from_utf8(&output.stdout).unwrap());

    parse_and_check_solver_proof(pool, problem.as_bytes(), proof)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))
}

/// Given a string "(-)?[0-9]+" returns a pair with the polarity (true if no leading minus) and the digit string
pub fn _get_pol_var(lit: String) -> (bool, i32) {
    if lit.starts_with("-") {
        (false, lit[1..lit.len()].parse::<i32>().unwrap())
    } else {
        (true, lit.parse::<i32>().unwrap())
    }
}

fn gen_dimacs<'a>(
    premise_clauses: &'a Vec<Vec<Rc<Term>>>,
    clause_id_to_lemma: &HashMap<usize, Rc<Term>>,
    sat_clause_to_lemma: &mut HashMap<Vec<i32>, Rc<Term>>,
    mark_lemmas: bool,
) -> String {
    let mut clauses: String = "".to_string();
    let mut max_var = 0;
    let mut lemma_id = 0;

    use std::fmt::Write;

    let mut term_to_var: HashMap<&Rc<Term>, i32> = HashMap::new();

    for i in 0..premise_clauses.len() {
        let is_lemma = clause_id_to_lemma.contains_key(&i);
        if mark_lemmas && is_lemma {
            clauses += &format!("@l{} ", lemma_id).to_owned();
            lemma_id += 1;
        }
        let mut clause_lits = Vec::new();
        premise_clauses[i].iter().for_each(|lit| {
            let (pol, term) = lit.remove_all_negations_with_polarity();
            if !term_to_var.contains_key(term) {
                term_to_var.insert(term, max_var + 1);
                max_var += 1;
            }
            clause_lits.push(if !pol {
                -term_to_var[term]
            } else {
                term_to_var[term]
            });
            clauses += &format!("{} ", clause_lits[clause_lits.len() - 1]).to_owned();
        });
        if is_lemma {
            clause_lits.sort();
            sat_clause_to_lemma.insert(clause_lits, clause_id_to_lemma[&i].clone());
        }
        writeln!(&mut clauses, "0").unwrap();
    }
    let mut dimacs = String::new();
    writeln!(&mut dimacs, "p cnf {} {}", max_var, premise_clauses.len()).unwrap();
    write!(&mut dimacs, "{}", clauses).unwrap();
    // let cnf_path = format!("{}.cnf", process::id());
    let cnf_path = "proof.cnf".to_string();
    write!(File::create(cnf_path.clone()).unwrap(), "{}", dimacs).unwrap();
    cnf_path
}

pub fn collect_premise_clauses(
    pool : &mut dyn TermPool,
    premise_steps: &Vec<&ProofCommand>,
    lemmas : &mut Vec<Rc<Term>>,
    clause_id_to_lemma: &mut HashMap<usize, Rc<Term>>
) -> Vec<Vec<Rc<Term>>> {
    let mut premise_clauses: Vec<Vec<_>> = Vec::new();
    let mut _or_lits : Vec<Rc<Term>> = Vec::new();
    premise_steps.iter().for_each(|p| {
        match p {
            ProofCommand::Step(step) => {
                // holes are assumed to be theory lemmas, where if they
                // are OR nodes then they are non-unit, otherwise
                // unities. If they are not singleton clauses, we add the
                // whole clause as a clause
                if step.rule == "hole" {
                    match &step.clause[..] {
                        [term] => match term.as_ref() {
                            Term::Op(Operator::Or, or_args) => {
                                premise_clauses.push(or_args.to_vec());
                                lemmas
                                    .push(pool.add(Term::Op(Operator::RareList, or_args.to_vec())));
                                // or_args.iter().for_each(|lit| {
                                //     match lit.as_op() {
                                //         Some((Operator::Or, _)) => { or_lits.push(lit.clone()); },
                                //         Some((Operator::Not, not_args)) => {
                                //             if let Some((Operator::Or, _)) = not_args[0].as_op() {
                                //                 or_lits.push(not_args[0].clone());
                                //             }

                                //         },
                                //         _ => {}
                                //     }
                                // }
                                // );
                            }
                            _ => {
                                premise_clauses.push(vec![term.clone()]);
                                lemmas.push(
                                    pool.add(Term::Op(Operator::RareList, vec![term.clone()])),
                                );
                                // step.clause.iter().for_each(|lit| {
                                //     match lit.as_op() {
                                //         Some((Operator::Or, _)) => { or_lits.push(lit.clone()); },
                                //         Some((Operator::Not, not_args)) => {
                                //             if let Some((Operator::Or, _)) = not_args[0].as_op() {
                                //                 or_lits.push(not_args[0].clone());
                                //             }

                                //         },
                                //         _ => {}
                                //     }
                                // }
                                // );
                            }
                        },
                        _ => {
                            premise_clauses.push(step.clause.clone());
                            lemmas
                                .push(pool.add(Term::Op(Operator::RareList, step.clause.clone())));
                            // step.clause.iter().for_each(|lit| {
                            //         match lit.as_op() {
                            //             Some((Operator::Or, _)) => { or_lits.push(lit.clone()); },
                            //             Some((Operator::Not, not_args)) => {
                            //                 if let Some((Operator::Or, _)) = not_args[0].as_op() {
                            //                     or_lits.push(not_args[0].clone());
                            //                 }

                            //             },
                            //             _ => {}
                            //         }
                            //     }
                            //     );
                        }
                    };
                    clause_id_to_lemma
                        .insert(premise_clauses.len() - 1, lemmas[lemmas.len() - 1].clone());
                } else {
                    match &step.clause[..] {
                        // singletons are always added as unities and as clauses, if OR nodes
                        [term] => {
                            match term.as_ref() {
                                Term::Op(Operator::Or, or_args) => {
                                    // add as a non-singleton clause
                                    premise_clauses.push(or_args.to_vec());
                                    // or_args.iter().for_each(|lit| {
                                    // match lit.as_op() {
                                    //     Some((Operator::Or, _)) => { or_lits.push(lit.clone()); },
                                    //     Some((Operator::Not, not_args)) => {
                                    //         if let Some((Operator::Or, _)) = not_args[0].as_op() {
                                    //             or_lits.push(not_args[0].clone());
                                    //         }

                                    //     },
                                    //     _ => {}
                                    // }
                                    // }
                                    // );
                                }
                                _ => {}
                            }
                            premise_clauses.push(vec![term.clone()]);
                        }
                        _ => {
                            premise_clauses.push(step.clause.clone());
                            // step.clause.iter().for_each(|lit| {
                            //         match lit.as_op() {
                            //             Some((Operator::Or, _)) => { or_lits.push(lit.clone()); },
                            //             Some((Operator::Not, not_args)) => {
                            //                 if let Some((Operator::Or, _)) = not_args[0].as_op() {
                            //                     or_lits.push(not_args[0].clone());
                            //                 }

                            //             },
                            //             _ => {}
                            //         }
                            //     }
                            //     );
                        }
                    }
                }
            }
            ProofCommand::Subproof(_) => {}
            ProofCommand::Assume { term, .. } => {
                // if OR, collect as clause, but also always generate as
                // literal
                match term.as_ref() {
                    Term::Op(Operator::Or, or_args) => {
                        premise_clauses.push(or_args.to_vec());
                    }
                    _ => {}
                }
                premise_clauses.push(vec![term.clone()]);
            }
        }
    });
    println!(
        "CNF with {} clauses of which {} are lemmas",
        premise_clauses.len(),
        lemmas.len()
    );
    premise_clauses
}

pub fn get_core_lemmas(
    cnf_path : String,
    sat_clause_to_lemma: &HashMap<Vec<i32>, Rc<Term>>,
) -> {
    // not gonna pass input via stdin because in that case
    // CaDiCaL gets confused with receiving the name of the
    // proof file as an argument. If we could get the proof in
    // stdout then there would be no need to write a CNF file nor a DRAT file
    let cadical_process =
        Command::new("/home/hbarbosa/carcara/wt-cvc5/cadical/build/cadical")
        .args([
            cnf_path.clone(),
            "proof.drat".to_string(),
            "--no-binary".to_string(),
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    let output = cadical_process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;
    println!("Checking CNF {} with CaDiCaL", cnf_path);

    // CaDiCaL's exit code when successful is 10/20 (for
    // sat/unsat), so this will not lead to a successful
    // output according to Rust. So the test here directly
    // checks stdout to see if the problem is found unsat.
    if let Ok(stdout) = std::str::from_utf8(&output.stdout) {
        if !stdout.contains("s UNSATISFIABLE") {
            return Err(CheckerError::LiaGeneric(LiaGenericError::OutputNotUnsat));
        }
    } else {
        return Err(CheckerError::LiaGeneric(
            LiaGenericError::SolverGaveInvalidOutput,
        ));
    }
    // pass cnf + proof to drat-trim
    let drattrim_process = Command::new(
        "/home/hbarbosa/carcara/wt-cvc5/SMT-theory-trim/theory-trim/drat-trim",
    )
        .args([
            cnf_path.clone(),
            "proof.drat".to_string(),
            "-c".to_string(),
            "proof.core".to_string(),
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    println!("Checking DRAT with DRAT-trim");
    let output_drattrim = drattrim_process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;
    if !output_drattrim.status.success() {
        return Err(CheckerError::LiaGeneric(LiaGenericError::OutputNotUnsat));
    }

    let mut core_lemmas: Vec<Vec<Rc<Term>>> = Vec::new();
    fs::read_to_string("proof.core")
        .unwrap() // panic on possible file-reading errors
        .lines() // split the string into an iterator of string slices
        .skip(1)
        .for_each(|l| {
            let mut sat_clause_lits: Vec<i32> = String::from(l)
                .split(" ")
                .filter_map(|lit| match lit.parse::<i32>() {
                    Ok(lit) if lit != 0 => Some(lit),
                    _ => None,
                })
                .collect();
            sat_clause_lits.sort();
            if let Some(lemma) = sat_clause_to_lemma.get(&sat_clause_lits) {
                if let Some((Operator::RareList, lemma_lits)) = lemma.as_op() {
                    core_lemmas.push(lemma_lits.to_vec().clone());
                }
            }
        });
    println!("{} lemmas in core", core_lemmas.len());

    core_lemmas
}
