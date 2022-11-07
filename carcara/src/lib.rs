#![deny(clippy::disallowed_methods)]
#![deny(clippy::self_named_module_files)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::branches_sharing_code)]
#![warn(clippy::cloned_instead_of_copied)]
#![warn(clippy::copy_iterator)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::doc_markdown)]
#![warn(clippy::equatable_if_let)]
#![warn(clippy::eval_order_dependence)]
#![warn(clippy::explicit_into_iter_loop)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::from_iter_instead_of_collect)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::if_not_else)]
#![warn(clippy::implicit_clone)]
#![warn(clippy::inconsistent_struct_constructor)]
#![warn(clippy::index_refutable_slice)]
#![warn(clippy::inefficient_to_string)]
#![warn(clippy::items_after_statements)]
#![warn(clippy::large_types_passed_by_value)]
#![warn(clippy::manual_assert)]
#![warn(clippy::manual_ok_or)]
#![warn(clippy::map_unwrap_or)]
#![warn(clippy::match_wildcard_for_single_variants)]
#![warn(clippy::multiple_crate_versions)]
#![warn(clippy::redundant_closure_for_method_calls)]
#![warn(clippy::redundant_pub_crate)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::trivially_copy_pass_by_ref)]
#![warn(clippy::unnecessary_wraps)]
#![warn(clippy::unnested_or_patterns)]
#![warn(clippy::unused_self)]

#[macro_use]
pub mod ast;
pub mod benchmarking;
pub mod checker;
pub mod parser;
mod utils;

use ast::ProofCommand;
use checker::error::CheckerError;
use parser::ParserError;
use parser::Position;
use std::io;
use thiserror::Error;

pub type CarcaraResult<T> = Result<T, Error>;

pub struct CarcaraOptions {
    pub apply_function_defs: bool,
    pub allow_int_real_subtyping: bool,
    pub check_lia_using_cvc5: bool,
    pub strict: bool,
    pub skip_unknown_rules: bool,
}

impl Default for CarcaraOptions {
    fn default() -> Self {
        Self::new()
    }
}

impl CarcaraOptions {
    fn new() -> Self {
        Self {
            apply_function_defs: true,
            allow_int_real_subtyping: false,
            check_lia_using_cvc5: false,
            strict: false,
            skip_unknown_rules: false,
        }
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("parser error: {0} (on line {}, column {})", (.1).0, (.1).1)]
    Parser(ParserError, Position),

    #[error("checking failed on step '{step}' with rule '{rule}': {inner}")]
    Checker {
        inner: CheckerError,
        rule: String,
        step: String,
    },

    // While this is a kind of checking error, it does not happen in a specific step like all other
    // checker errors, so we model it as a different variant
    #[error("checker error: proof does not conclude empty clause")]
    DoesNotReachEmptyClause,
}

pub fn check<T: io::BufRead>(
    problem: T,
    proof: T,
    CarcaraOptions {
        apply_function_defs,
        allow_int_real_subtyping,
        check_lia_using_cvc5,
        strict,
        skip_unknown_rules,
    }: CarcaraOptions,
) -> Result<bool, Error> {
    let (prelude, proof, mut pool) = parser::parse_instance(
        problem,
        proof,
        apply_function_defs,
        allow_int_real_subtyping,
    )?;

    let config = checker::Config {
        strict,
        skip_unknown_rules,
        is_running_test: false,
        statistics: None,
        check_lia_using_cvc5,
    };
    checker::ProofChecker::new(&mut pool, config, prelude).check(&proof)
}

pub fn check_and_elaborate<T: io::BufRead>(
    problem: T,
    proof: T,
    CarcaraOptions {
        apply_function_defs,
        allow_int_real_subtyping,
        check_lia_using_cvc5,
        strict,
        skip_unknown_rules,
    }: CarcaraOptions,
) -> Result<Vec<ProofCommand>, Error> {
    let (prelude, proof, mut pool) = parser::parse_instance(
        problem,
        proof,
        apply_function_defs,
        allow_int_real_subtyping,
    )?;

    let config = checker::Config {
        strict,
        skip_unknown_rules,
        is_running_test: false,
        statistics: None,
        check_lia_using_cvc5,
    };
    checker::ProofChecker::new(&mut pool, config, prelude)
        .check_and_elaborate(proof)
        .map(|p| p.commands)
}

pub fn generate_lia_smt_instances<T: io::BufRead>(
    problem: T,
    proof: T,
    apply_function_defs: bool,
    use_sharing: bool,
    allow_int_real_subtyping: bool,
) -> Result<Vec<(String, String)>, Error> {
    let (prelude, proof, _) = parser::parse_instance(
        problem,
        proof,
        apply_function_defs,
        allow_int_real_subtyping,
    )?;
    checker::generate_lia_smt_instances(prelude, &proof, use_sharing)
}