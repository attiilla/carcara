use super::*;
use crate::{checker, parser, CarcaraResult};
use crate::checker::error::LiaGenericError;
use std::collections::HashMap;
use std::fs;
use std::process;
use std::{
    any::Any,
    fs::File,
    io::{BufRead, Write},
    process::{Command, Stdio},
};

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

    println!("{}", problem);
    println!("{}", std::str::from_utf8(&output.stdout).unwrap());

    parse_and_check_solver_proof(pool, problem.as_bytes(), proof)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))
}

/// Given a string "(-)?[0-9]+" returns a pair with the polarity (true if no leading minus) and the digit string
pub fn get_pol_var(lit: String) -> (bool, usize) {
    if lit.starts_with("-") {
        (false, lit[1..lit.len()].parse::<usize>().unwrap())
    } else {
        (true, lit.parse::<usize>().unwrap())
    }
}

fn gen_dimacs<'a>(
    premise_clauses: &'a Vec<Vec<Rc<Term>>>,
    clause_id_to_lemma: &HashMap<usize, Rc<Term>>,
    term_to_var: &mut HashMap<&'a Rc<Term>, usize>,
    mark_lemmas: bool,
) -> String {
    let mut clauses: String = "".to_string();
    let mut max_var = 0;
    let mut lemma_id = 0;

    use std::fmt::Write;

    for i in 0..premise_clauses.len() {
        if mark_lemmas && clause_id_to_lemma.contains_key(&i) {
            clauses += &format!("@l{} ", lemma_id).to_owned();
            lemma_id += 1;
        }
        premise_clauses[i].iter().for_each(|lit| {
            let (pol, term) = lit.remove_all_negations_with_polarity();
            if !term_to_var.contains_key(term) {
                term_to_var.insert(term, max_var + 1);
                max_var += 1;
            }
            clauses += &format!("{}{} ", if !pol { "-" } else { "" }, term_to_var[term]).to_owned();
        });
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

fn sat_refutation_external_check(
    cnf_path: String,
    prelude: &ProblemPrelude,
    checker_path: String,
    lemmas: &Vec<Rc<Term>>,
) -> RuleResult {
    let prelude_path = format!("prelude_{}.smt2", process::id());
    write!(File::create(prelude_path.clone()).unwrap(), "{}", prelude).unwrap();

    // transform each AND arg, if any, into a string and build a
    // string "(and ... )" so that each lemma has its own names
    let lemmas_as_str = if lemmas.len() == 1 {
        let lemma_or = if let Some((Operator::RareList, lemma_lits)) = lemmas[0].as_op() {
            Term::Op(Operator::Or, lemma_lits.to_vec())
        } else {
            unreachable!();
        };
        format!("{}", lemma_or)
    } else {
        let mut str_aux = String::new();
        use std::fmt::Write;
        write!(&mut str_aux, "(and").unwrap();
        lemmas.iter().for_each(|lemma| {
            let lemma_or = if let Some((Operator::RareList, lemma_lits)) = lemma.as_op() {
                Term::Op(Operator::Or, lemma_lits.to_vec())
            } else {
                unreachable!();
            };
            write!(&mut str_aux, " {}", lemma_or).unwrap();
        });
        write!(&mut str_aux, ")").unwrap();
        str_aux
    };

    let string = format!("(\n{}\n{}\n{}\n)", cnf_path, prelude_path, lemmas_as_str);
    // this will make it expect this script from where you are running Carcara
    let mut process = Command::new(checker_path.clone())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(string.as_bytes())
        .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(CheckerError::Unspecified);
            }
        }
        return Err(CheckerError::Unspecified);
    }
    let res = output.stdout.as_slice();

    if res == b"true\n" {
        return Ok(());
    }
    return Err(CheckerError::Explanation(format!(
        "External checker {} did not validate step",
        checker_path
    )));
}

pub fn sat_refutation(
    RuleArgs { pool, .. }: RuleArgs,
    premise_steps: Vec<&ProofCommand>,
    prelude: &ProblemPrelude,
    checker_path: Option<String>,
) -> RuleResult {
    // Create the DIMACS file from the premises and the lemmas.
    //
    // Lemmas (i.e., conclusions of "hole") are non-unit clauses if
    // they are OR terms, and unit otherwise. Literals are going to be
    // generated by doing the "remove_all_negations()" method of
    // terms.
    //
    // For the remaining premises, we can have some of them which
    // occur as arguments in others, which as a safer thing we also
    // add them as unit clauses with a literal corresponding to the
    // whole clause.
    let mut lemmas: Vec<Rc<Term>> = Vec::new();
    let mut premise_clauses: Vec<Vec<_>> = Vec::new();
    let mut clause_id_to_lemma: HashMap<usize, Rc<Term>> = HashMap::new();
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
                            }
                            _ => {
                                premise_clauses.push(vec![term.clone()]);
                                lemmas.push(
                                    pool.add(Term::Op(Operator::RareList, vec![term.clone()])),
                                );
                            }
                        },
                        _ => {
                            premise_clauses.push(step.clause.clone());
                            lemmas
                                .push(pool.add(Term::Op(Operator::RareList, step.clause.clone())));
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
                                    premise_clauses.push(or_args.to_vec());
                                }
                                _ => {}
                            }
                            premise_clauses.push(vec![term.clone()]);
                        }
                        _ => {
                            premise_clauses.push(step.clause.clone());
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

    let mut term_to_var: HashMap<&Rc<Term>, usize> = HashMap::new();
    match checker_path {
        Some(checker_path) => {
            let cnf_path = gen_dimacs(
                &premise_clauses,
                &clause_id_to_lemma,
                &mut term_to_var,
                true,
            );
            sat_refutation_external_check(cnf_path, prelude, checker_path, &lemmas)
        }
        None => {
            let cnf_path = gen_dimacs(
                &premise_clauses,
                &clause_id_to_lemma,
                &mut term_to_var,
                false,
            );

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

            let output_drattrim = drattrim_process
                .wait_with_output()
                .map_err(LiaGenericError::FailedWaitForSolver)?;
            if !output_drattrim.status.success() {
                return Err(CheckerError::LiaGeneric(LiaGenericError::OutputNotUnsat));
            }

            let var_to_term: HashMap<&usize, &Rc<Term>> =
                term_to_var.iter().map(|(k, v)| (v, k.clone())).collect();
            let mut core_lemmas: Vec<Vec<Rc<Term>>> = Vec::new();
            fs::read_to_string("proof.core")
                .unwrap() // panic on possible file-reading errors
                .lines() // split the string into an iterator of string slices
                .skip(1)
                .for_each(|l| {
                    let clause_lits: Vec<Rc<Term>> = String::from(l)
                        .split(" ")
                        .filter(|lit| lit != &"0")
                        .map(|lit| {
                            let (pol, var) = get_pol_var(lit.to_string());
                            if pol {
                                var_to_term[&var].clone()
                            } else {
                                pool.add(Term::Op(Operator::Not, vec![var_to_term[&var].clone()]))
                            }
                        })
                        .collect();
                    let clause = pool.add(Term::Op(Operator::RareList, clause_lits.clone()));
                    let is_lemma = lemmas
                        .iter()
                        .find(|lemma| lemma.clone().clone() == clause)
                        .is_some();
                    println!(
                        "{}{} : {:?}",
                        if is_lemma { "(lemma) " } else { "" },
                        l,
                        clause_lits
                    );
                    if is_lemma {
                        core_lemmas.push(clause_lits.clone());
                    }
                });

            let mut dunno = Box::new(pool);
            let crazy_pool: &mut PrimitivePool =
                match dunno.as_any_mut().downcast_mut::<PrimitivePool>() {
                    Some(b) => b,
                    None => panic!("&a isn't a B!"),
                };
            // for each core lemma, we will run cvc5, parse the proof in, and check it
            let mut unchecked_lemmas = Vec::new();
            core_lemmas.iter().for_each(|lemma| {
                let problem = get_problem_string(crazy_pool, &prelude, lemma);

                if let Err(_) = get_solver_proof(crazy_pool, problem.clone()) {
                    unchecked_lemmas.push(lemma);
                }
            });
            if !unchecked_lemmas.is_empty() {
                return Err(CheckerError::LiaGeneric(LiaGenericError::OutputNotUnsat));
            }
            Ok(())

            // fs::remove_file(cnf_path);
            // fs::remove_file("proof.drat");

        }
    }
}

pub fn external_checker(RuleArgs { args, .. }: RuleArgs, checker_path: String) -> RuleResult {
    let args_str: Vec<String> = args.iter().map(|t| format!("{}", t)).collect();
    let string = format!("(\n{}\n)", args_str.join("\n"));
    // this will make it expect this script from where you are running Carcara
    let mut process = Command::new(checker_path.clone())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(string.as_bytes())
        .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(CheckerError::Unspecified);
            }
        }
        return Err(CheckerError::Unspecified);
    }
    let res = output.stdout.as_slice();
    if res == b"true\n" {
        return Ok(());
    }
    return Err(CheckerError::Explanation(format!(
        "External checker {} did not validate step",
        checker_path
    )));
}
