//! The abstract syntax tree (AST) for the Alethe proof format.
//!
//! This module also contains various utilities for manipulating Alethe proofs and terms.

#[macro_use]
mod macros;
mod context;
mod iter;
mod polyeq;
pub mod pool;
pub(crate) mod printer;
mod rc;
mod substitution;
#[cfg(test)]
mod tests;

pub use context::{Context, ContextStack};
pub use iter::ProofIter;
pub use polyeq::{alpha_equiv, polyeq, polyeq_mod_nary, tracing_polyeq_mod_nary};
pub use pool::{PrimitivePool, TermPool};
pub use printer::{print_proof, USE_SHARING_IN_TERM_DISPLAY};
pub use rc::Rc;
pub use substitution::{Substitution, SubstitutionError};

pub(crate) use polyeq::{Polyeq, PolyeqComparator};

use crate::checker::error::CheckerError;
use indexmap::{IndexSet, IndexMap};
use rug::Integer;
use rug::Rational;
use std::{hash::Hash, ops::Deref};

/// The prelude of an SMT-LIB problem instance.
///
/// This stores the sort declarations, function declarations and the problem's logic string.
#[derive(Debug, Clone, Default)]
pub struct ProblemPrelude {
    /// The sort declarations, each represented by its name and arity.
    pub(crate) sort_declarations: Vec<(String, usize)>,

    /// The function declarations, each represented by its name and body.
    pub(crate) function_declarations: Vec<(String, Rc<Term>)>,

    /// The problem's logic string, if it exists.
    pub(crate) logic: Option<String>,
}

/// A proof in the Alethe format.
#[derive(Debug, Clone)]
pub struct Proof {
    /// The proof's premises.
    ///
    /// Those are the terms introduced in the original problem's `assert` commands.
    pub premises: IndexSet<Rc<Term>>,

    /// The proof commands.
    pub commands: Vec<ProofCommand>,
}

impl Proof {
    /// Returns an iterator over the proof commands. See [`ProofIter`].
    pub fn iter(&self) -> ProofIter {
        ProofIter::new(&self.commands)
    }
}

/// A proof command.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofCommand {
    /// An `assume` command.
    Assume { id: String, term: Rc<Term> },

    /// A `step` command.
    Step(ProofStep),

    /// A subproof.
    Subproof(Subproof),
}

impl ProofCommand {
    /// Returns the unique id of this command.
    ///
    /// For subproofs, this is the id of the last step in the subproof.
    pub fn id(&self) -> &str {
        match self {
            ProofCommand::Assume { id, .. } => id,
            ProofCommand::Step(s) => &s.id,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().id(),
        }
    }

    /// Returns the clause of this command.
    ///
    /// For `assume` commands, this is a unit clause containing the assumed term; for steps, it's
    /// the conclusion clause; and for subproofs, it's the conclusion clause of the last step in the
    /// subproof.
    pub fn clause(&self) -> &[Rc<Term>] {
        match self {
            ProofCommand::Assume { id: _, term } => std::slice::from_ref(term),
            ProofCommand::Step(ProofStep { clause, .. }) => clause,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().clause(),
        }
    }

    /// Returns `true` if the command is an `assume` command.
    pub fn is_assume(&self) -> bool {
        matches!(self, ProofCommand::Assume { .. })
    }

    /// Returns `true` if the command is a `step` command.
    pub fn is_step(&self) -> bool {
        matches!(self, ProofCommand::Step(_))
    }

    /// Returns `true` if the command is a subproof.
    pub fn is_subproof(&self) -> bool {
        matches!(self, ProofCommand::Subproof(_))
    }
}

/// A `step` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// The step id.
    pub id: String,

    /// The conclusion clause.
    pub clause: Vec<Rc<Term>>,

    /// The rule used by the step.
    pub rule: String,

    /// The premises of the step, given via the `:premises` attribute.
    ///
    /// Each premise references a command, indexed using two indices: The first indicates the depth
    /// of the subproof where the command is located, in the stack of currently open subproofs. The
    /// second is the index of the command in that subproof.
    pub premises: Vec<(usize, usize)>,

    /// The step arguments, given via the `:args` attribute.
    pub args: Vec<ProofArg>,

    /// The local premises that this step discharges, given via the `:discharge` attribute, and
    /// indexed similarly to premises.
    pub discharge: Vec<(usize, usize)>,
}

/// A subproof.
///
/// Subproofs are started by `anchor` commands, and contain a series of steps, possibly including
/// nested subproofs. A subproof must end in a `step`, which is indicated in the anchor via the
/// `:step` attribute.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Subproof {
    /// The proof commands inside the subproof.
    pub commands: Vec<ProofCommand>,

    /// The "assignment" style arguments of the subproof, of the form `(:= <symbol> <term>)`.
    pub assignment_args: Vec<(String, Rc<Term>)>,

    /// The "variable" style arguments of the subproof, of the form `(<symbol> <sort>)`.
    pub variable_args: Vec<SortedVar>,

    /// Subproof id used for context hashing purpose
    pub context_id: usize,
}

/// An argument for a `step` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofArg {
    /// An argument that is just a term.
    Term(Rc<Term>),

    /// An argument of the form `(:= <symbol> <term>)`.
    Assign(String, Rc<Term>),
}

impl ProofArg {
    /// If this argument is a "term style" argument, extracts that term from it. Otherwise, returns
    /// an error.
    pub fn as_term(&self) -> Result<&Rc<Term>, CheckerError> {
        match self {
            ProofArg::Term(t) => Ok(t),
            ProofArg::Assign(s, t) => Err(CheckerError::ExpectedTermStyleArg(s.clone(), t.clone())),
        }
    }

    /// If this argument is an "assign style" argument, extracts the variable name and the value
    /// term from it. Otherwise, returns an error.
    pub fn as_assign(&self) -> Result<(&String, &Rc<Term>), CheckerError> {
        match self {
            ProofArg::Assign(s, t) => Ok((s, t)),
            ProofArg::Term(t) => Err(CheckerError::ExpectedAssignStyleArg(t.clone())),
        }
    }
}

/// The operator of an operation term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    /// The `true` boolean constant.
    True,

    /// The `false` boolean constant.
    False,

    // Logic
    /// The `not` operator.
    Not,

    /// The `=>` operator.
    Implies,

    /// The `and` operator.
    And,

    /// The `or` operator.
    Or,

    /// The `xor` operator.
    Xor,

    /// The `=` operator.
    Equals,

    /// The `distinct` operator.
    Distinct,

    /// The `ite` operator.
    Ite,

    // Arithmetic
    /// The `+` operator.
    Add,

    /// The `-` operator.
    Sub,

    /// The `*` operator.
    Mult,

    /// The `div` operator.
    IntDiv,

    /// The `/` operator.
    RealDiv,

    /// The `mod` operator.
    Mod,

    /// The `abs` operator.
    Abs,

    /// The `<` operator.
    LessThan,

    /// The `>` operator.
    GreaterThan,

    /// The `<=` operator.
    LessEq,

    /// The `>=` operator.
    GreaterEq,

    /// The `to_real` operator.
    ToReal,

    /// The `to_int` operator.
    ToInt,

    /// The `is_int` operator.
    IsInt,

    // Arrays
    /// The `select` operator.
    Select,

    /// The `store` operator.
    Store,

    // Strings
    /// The `str.++` operator.
    StrConcat,

    /// The `str.len` operator.
    StrLen,

    /// The `str.<` operator.
    StrLessThan,

    /// The `str.<=` operator.
    StrLessEq,

    /// The `str.at` operator.
    CharAt,

    /// The `str.substr` operator.
    Substring,

    /// The `str.prefixof` operator.
    PrefixOf,

    /// The `str.suffixof` operator.
    SuffixOf,

    /// The `str.contains` operator.
    Contains,

    /// The `str.indexof` operator.
    IndexOf,

    /// The `str.replace` operator.
    Replace,

    /// The `str.replace_all` operator.
    ReplaceAll,

    /// The `str.replace_re` operator.
    ReplaceRe,

    /// The `str.replace_re_all` operator.
    ReplaceReAll,

    /// The `str.is_digit` operator.
    StrIsDigit,

    /// The `str.to_code` operator.
    StrToCode,

    /// The `str.from_code` operator.
    StrFromCode,

    /// The `str.to_int` operator.
    StrToInt,

    /// The `str.from_int` operator.
    StrFromInt,

    // Regular Expressions
    /// The `str.to_re` operator.
    StrToRe,

    /// The `str.in_re` operator.
    StrInRe,

    /// The `re.none` operator.
    ReNone,

    /// The `re.all` operator.
    ReAll,

    /// The `re.allchar` operator.
    ReAllChar,

    /// The `re.++` operator.
    ReConcat,

    /// The `re.union` operator.
    ReUnion,

    /// The `re.inter` operator.
    ReIntersection,

    /// The `re.*` operator.
    ReKleeneClosure,

    /// The `re.comp` operator.
    ReComplement,

    /// The `re.diff` operator.
    ReDiff,

    /// The `re.+` operator.
    ReKleeneCross,

    /// The `re.opt` operator.
    ReOption,

    /// The `re.range` operator.
    ReRange,

    // BV operators (unary)
    BvNot,
    BvNeg,
    // BV operators (binary, left-assoc)
    BvAnd,
    BvOr,
    BvAdd,
    BvMul,
    // BV operators (binary)
    BvUDiv,
    BvURem,
    BvShl,
    BvLShr,
    BvULt,

    BvConcat,
    BvNAnd,
    BvNOr,
    BvXor,
    BvXNor,
    BvComp,
    BvSub,
    BvSDiv,
    BvSRem,
    BvSMod,
    BvAShr,

    BvULe,
    BvUGt,
    BvUGe,
    BvSLt,
    BvSLe,
    BvSGt,
    BvSGe,
    Bv2Nat,

    BvBbTerm,

    // Misc.
    /// The `rare-list` operator, used to represent RARE lists.
    RareList,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParamOperator {
    // Indexed operators
    BvExtract,
    ZeroExtend,
    SignExtend,
    RotateLeft,
    RotateRight,
    Repeat,
    BvConst,

    Int2BV,

    BvBitOf,

    RePower,
    ReLoop,

    // Datatypes,
    Tester,

    // Qualified operators
    ArrayConst,
}

impl_str_conversion_traits!(ParamOperator {
    BvExtract: "extract",
    BvBitOf: "bitOf",
    ZeroExtend: "zero_extend",
    SignExtend: "sign_extend",
    RotateLeft: "rotate_left",
    RotateRight: "rotate_right",
    Repeat: "repeat",
    BvConst: "bv",

    Int2BV: "int2bv",

    RePower: "re.^",
    ReLoop: "re.loop",

    Tester: "is",

    ArrayConst: "const",
});

impl_str_conversion_traits!(Operator {
    True: "true",
    False: "false",

    Not: "not",
    Implies: "=>",
    And: "and",
    Or: "or",
    Xor: "xor",
    Equals: "=",
    Distinct: "distinct",
    Ite: "ite",

    Add: "+",
    Sub: "-",
    Mult: "*",
    IntDiv: "div",
    RealDiv: "/",
    Mod: "mod",
    Abs: "abs",
    LessThan: "<",
    GreaterThan: ">",
    LessEq: "<=",
    GreaterEq: ">=",
    ToReal: "to_real",
    ToInt: "to_int",
    IsInt: "is_int",

    Select: "select",
    Store: "store",

    StrConcat: "str.++",
    StrLen: "str.len",
    StrLessThan: "str.<",
    StrLessEq: "str.<=",
    CharAt: "str.at",
    Substring: "str.substr",
    PrefixOf: "str.prefixof",
    SuffixOf: "str.suffixof",
    Contains: "str.contains",
    IndexOf: "str.indexof",
    Replace: "str.replace",
    ReplaceAll: "str.replace_all",
    ReplaceRe: "str.replace_re",
    ReplaceReAll: "str.replace_re_all",
    StrIsDigit: "str.is_digit",
    StrToCode: "str.to_code",
    StrFromCode: "str.from_code",
    StrToInt: "str.to_int",
    StrFromInt: "str.from_int",

    StrToRe: "str.to_re",
    StrInRe: "str.in_re",
    ReNone: "re.none",
    ReAll: "re.all",
    ReAllChar: "re.allchar",
    ReConcat: "re.++",
    ReUnion: "re.union",
    ReIntersection: "re.inter",
    ReKleeneClosure: "re.*",
    ReComplement: "re.comp",
    ReDiff: "re.diff",
    ReKleeneCross: "re.+",
    ReOption: "re.opt",
    ReRange: "re.range",
    BvNot: "bvnot",
    BvNeg: "bvneg",
    BvAnd: "bvand",
    BvOr: "bvor",
    BvAdd: "bvadd",
    BvMul: "bvmul",
    BvUDiv: "bvudiv",
    BvURem: "bvurem",
    BvShl: "bvshl",
    BvLShr: "bvlshr",
    BvULt: "bvult",

    BvConcat: "concat",
    BvNAnd: "bvnand",
    BvNOr: "bvnor",
    BvXor: "bvxor",
    BvXNor: "bvxnor",
    BvComp: "bvcomp",
    BvSub: "bvsub",
    BvSDiv: "bvsdiv",
    BvSRem: "bvsrem",
    BvSMod: "bvsmod",
    BvAShr: "bvashr",

    BvULe: "bvule",
    BvUGt: "bvugt",
    BvUGe: "bvuge",
    BvSLt: "bvslt",
    BvSLe: "bvsle",
    BvSGt: "bvsgt",
    BvSGe: "bvsge",
    Bv2Nat: "bv2nat",
    BvBbTerm: "bbT",

    RareList: "rare-list",
});

/// A variable and an associated sort.
pub type SortedVar = (String, Rc<Term>);

/// The sort of a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// A function sort.
    ///
    /// The last term indicates the return sort of the function. The remaining terms are the sorts
    /// of the parameters of the function.
    Function(Vec<Rc<Term>>),

    /// A user-declared sort, from a `declare-sort` command.
    ///
    /// The associated string is the sort name, and the associated terms are the sort arguments for
    /// this sort.
    Atom(String, Vec<Rc<Term>>),

    // A sort variable
    Var(String),

    /// The `Bool` primitive sort.
    Bool,

    /// The `Int` primitive sort.
    Int,

    /// The `Real` primitive sort.
    Real,

    /// The `String` primitive sort.
    String,

    /// The `RegLan` primitive sort.
    RegLan,

    /// An `Array` sort.
    ///
    /// The two associated terms are the sort arguments for this sort.
    Array(Rc<Term>, Rc<Term>),
    ///  `BitVec` sort.
    ///
    /// The associated term is the BV width of this sort.
    BitVec(Integer),

    /// A datatype sort only has its name and its type parameters
    Datatype(String, Vec<Rc<Term>>),

    /// A parametric sort, with a set of sort variables that can appear in the second argument.
    ParamSort(Vec<Rc<Term>>, Rc<Term>),

    /// The sort of RARE lists.
    RareList,

    /// The sort of sorts.
    Type,
}

/// A binder, either a quantifier (`forall` or `exists`), `choice`, or `lambda`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binder {
    /// The `forall` quantifier.
    Forall,

    /// The `exists` quantifier.
    Exists,

    /// The `choice` binder.
    Choice,

    /// The `lambda` binder.
    Lambda,
}

impl std::ops::Not for Binder {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Binder::Forall => Binder::Exists,
            Binder::Exists => Binder::Forall,
            _ => panic!("logical negation is only defined for quantifier binders"),
        }
    }
}

/// A list of bindings, where each binding is a variable associated with a term.
///
/// Depending on the context, it can be a "sort" binding list (like the ones present in quantifier
/// terms) where the associated term of each variable is its sort; or a "value" binding list (like
/// the ones present in `let` terms) where the associated term of each variable is its bound value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingList(pub Vec<SortedVar>);

impl AsRef<[SortedVar]> for BindingList {
    fn as_ref(&self) -> &[SortedVar] {
        &self.0
    }
}

impl Deref for BindingList {
    type Target = Vec<SortedVar>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> IntoIterator for &'a BindingList {
    type Item = &'a SortedVar;

    type IntoIter = std::slice::Iter<'a, SortedVar>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl BindingList {
    pub const EMPTY: &'static Self = &BindingList(Vec::new());
}

/// A term.
///
/// Many additional methods are implemented in [`Rc<Term>`].
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A constant term.
    Const(Constant),

    /// A variable, consisting of an identifier and a sort.
    Var(String, Rc<Term>),

    /// An application of a function to one or more terms.
    App(Rc<Term>, Vec<Rc<Term>>),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator, Vec<Rc<Term>>),

    /// A sort.
    Sort(Sort),

    /// A binder term. This can be either a quantifier term (`forall`/`exists`), a `choice` term, or
    /// a `lambda` term.
    Binder(Binder, BindingList, Rc<Term>),

    /// A `let` binder term.
    Let(BindingList, Rc<Term>),

    /// A parameterized operation term, that is, an operation term whose operator receives extra
    /// parameters.
    ///
    /// This can be either:
    /// - An `indexed` operation term, that uses an indexed operator denoted by the `(_ ...)`
    ///   syntax. In this case, the operator parameters must be constants.
    /// - A `qualified` operation term, that uses a qualified operator denoted by the `(as ...)`
    ///   syntax. In this case, the single operator parameter must be a sort.
    /// - A `tester` of a datatype constructor `C`, denoted by `(_ is C)`.
    ParamOp {
        op: ParamOperator,
        op_args: Vec<Rc<Term>>,
        args: Vec<Rc<Term>>,
    },
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Var(var.0, var.1)
    }
}

impl Sort {
    // Whether this sort can be unified with another. The map argument
    // will be a substitution of sort variables to sorts
    pub fn unify(&self, target : &Sort, map: &IndexMap<String, Sort>) -> bool {
        match (self, target) {
            (Sort::Var(a), Sort::Atom(_,_)) => {
                // TODO check that target is compatible with value associated to a, if any
                map.insert(a, target);
                true
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                if a != b { false } else {
                    let matching = sorts_a.iter().zip(&sorts_b)
                        .filter(|&(t_a, t_b)| {
                            let s_a = t_a.as_sort().unwrap();
                            let s_b = t_b.as_sort().unwrap();
                            s_a.unify(s_b, map)
                        })
                        .count();
                    matching == a.len() && matching == b.len()
                }
            }
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => {
                for (a_t, b_t) in sorts_a.iter().zip(sorts_b.iter()) {
                    let a_s = a_t.as_sort().unwrap();
                    let b_s = b_t.as_sort().unwrap();
                    if !a_s.unify(b_s, map, p) { return false; }
                }
                true
            }
            (Sort::Datatype(a,_), Datatype(b,_)) => a == b,
            (Sort::Bool, Sort::Bool)
                | (Sort::Int, Sort::Int)
                | (Sort::Real, Sort::Real)
                | (Sort::String, Sort::String)
                | (Sort::RegLan, Sort::RegLan)
                | (Sort::RareList, Sort::RareList)
                | (Sort::Type, Sort::Type) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                let s_x_a = x_a.as_sort().unwrap();
                let s_y_a = y_a.as_sort().unwrap();
                let s_x_b = x_b.as_sort().unwrap();
                let s_y_b = y_b.as_sort().unwrap();
                s_x_a.unify(s_x_b, map) && s_x_b.unify(s_x_b, map)
            }
            (Sort::BitVec(a), Sort::BitVec(b)) => a == b,
            _ => false,
        }
    }
}

impl Term {
    pub fn new_bool(value: impl Into<bool>) -> Self {
        let op = match value.into() {
            true => Operator::True,
            false => Operator::False,
        };
        Term::Op(op, Vec::new())
    }

    /// Constructs a new integer term.
    pub fn new_int(value: impl Into<Integer>) -> Self {
        Term::Const(Constant::Integer(value.into()))
    }

    /// Constructs a new real term.
    pub fn new_real(value: impl Into<Rational>) -> Self {
        Term::Const(Constant::Real(value.into()))
    }

    /// Constructs a new string term.
    pub fn new_string(value: impl Into<String>) -> Self {
        Term::Const(Constant::String(value.into()))
    }

    /// Constructs a new bv term.
    pub fn new_bv(value: impl Into<Integer>, width: impl Into<Integer>) -> Self
    {
        Term::Const(Constant::BitVec(value.into(), width.into()))
    }

    /// Constructs a new variable term.
    pub fn new_var(name: impl Into<String>, sort: Rc<Term>) -> Self {
        Term::Var(name.into(), sort)
    }

    /// Returns the sort of this term. This does not make use of a cache --- if possible, prefer to
    /// use `TermPool::sort`.
    pub fn raw_sort(&self) -> Sort {
        let mut pool = PrimitivePool::new();
        let added = pool.add(self.clone());
        pool.sort(&added).as_sort().unwrap().clone()
    }

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_number(&self) -> bool {
        matches!(self, Term::Const(Constant::Real(_) | Constant::Integer(_)))
    }

    /// Returns `true` if the term is an integer or real constant, or one such constant negated
    /// with the `-` operator.
    pub fn is_signed_number(&self) -> bool {
        match match_term!((-x) = self) {
            Some(x) => x.is_number(),
            None => self.is_number(),
        }
    }

    /// Tries to extract a `Rational` from a term. Returns `Some` if the term is an integer or real
    /// constant.
    pub fn as_number(&self) -> Option<Rational> {
        match self {
            Term::Const(Constant::Real(r)) => Some(r.clone()),
            Term::Const(Constant::Integer(i)) => Some(i.clone().into()),
            _ => None,
        }
    }

    /// Tries to extract a `bool` from a term. Returns `Some` if the term is a boolean constant.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Term::Op(Operator::True, _) => Some(true),
            Term::Op(Operator::False, _) => Some(false),
            _ => None,
        }
    }

    /// Tries to extract a `Integer` from a term. Returns `Some` if the term is an integer constant.
    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Term::Const(Constant::Integer(i)) => Some(i.clone()),
            _ => None,
        }
    }

    /// Tries to extract a `Rational` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer or real constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_number(&self) -> Option<Rational> {
        match match_term!((-x) = self) {
            Some(x) => x.as_number().map(|r| -r),
            None => self.as_number(),
        }
    }

    /// Tries to extract a `Integer` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_integer(&self) -> Option<Integer> {
        match match_term!((-x) = self) {
            Some(x) => x.as_integer().map(|r| -r),
            None => self.as_integer(),
        }
    }

    /// Tries to extract a `BitVec` from a term. Returns `Some` if the
    /// term is a bitvector constant.
    pub fn as_bitvector(&self) -> Option<(Integer, Integer)> {
        match self {
            Term::Const(Constant::BitVec(v, w)) => Some((v.clone(), w.clone())),
            _ => None,
        }
    }

    /// Tries to extract a `Rational` from a term, allowing fractions. This method will return
    /// `Some` if the term is:
    ///
    /// - A real or integer constant
    /// - An application of the `/` or `div` operators on two real or integer constants
    /// - An application of the unary `-` operator on one of the two previous cases
    pub fn as_fraction(&self) -> Option<Rational> {
        fn as_unsigned_fraction(term: &Term) -> Option<Rational> {
            match term {
                Term::Op(Operator::IntDiv | Operator::RealDiv, args) if args.len() == 2 => {
                    Some(args[0].as_signed_number()? / args[1].as_signed_number()?)
                }
                _ => term.as_number(),
            }
        }

        match match_term!((-x) = self) {
            Some(x) => as_unsigned_fraction(x).map(|r| -r),
            None => as_unsigned_fraction(self),
        }
    }

    /// Returns `true` if the term is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const(_))
    }

    /// Returns `true` if the term is a variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_, _))
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            Term::Var(var, _) => Some(var.as_str()),
            _ => None,
        }
    }

    /// Returns `true` if the term is a sort.
    pub fn is_sort(&self) -> bool {
        matches!(self, Term::Sort(_))
    }

    /// Tries to extract a sort from a term. Returns `Some` if the term is a sort.
    pub fn as_sort(&self) -> Option<&Sort> {
        match self {
            Term::Sort(s) => Some(s),
            _ => None,
        }
    }

    /// Returns `true` if the term is a user defined sort with arity zero, or a sort variable.
    pub fn is_sort_var(&self) -> bool {
        matches!(self, Term::Sort(Sort::Atom(_, args)) if args.is_empty())
    }

    /// Returns `true` if the term is a user defined parametric sort
    pub fn is_sort_parametric(&self) -> bool {
        match self {
            Term::Sort(Sort::ParamSort(_, _)) => true,
            Term::Sort(Sort::Datatype(_, args)) if !args.is_empty() => true,
            _ => false
        }
        // matches!(self, Term::Sort(Sort::ParamSort(_, _)))
    }

    /// Returns `true` if the term is a user defined sort with arity zero, or a sort variable.
    pub fn is_sort_dt(&self) -> bool {
        matches!(self, Term::Sort(Sort::Datatype(_, _)))
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns
    /// `None` if the term is not an operation term.
    pub fn as_op(&self) -> Option<(Operator, &[Rc<Term>])> {
        match self {
            Term::Op(op, args) => Some((*op, args.as_slice())),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Binder`, the bindings and the inner term.
    /// Returns `None` if the term is not a quantifier term.
    pub fn as_quant(&self) -> Option<(Binder, &BindingList, &Rc<Term>)> {
        match self {
            Term::Binder(q @ (Binder::Forall | Binder::Exists), b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Tries to unwrap a binder term, returning the `Binder`, the bindings and the inner term.
    /// Returns `None` if the term is not a binder term.
    pub fn as_binder(&self) -> Option<(Binder, &BindingList, &Rc<Term>)> {
        match self {
            Term::Binder(binder, bindings, inner) => Some((*binder, bindings, inner)),
            _ => None,
        }
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner term. Returns `None` if
    /// the term is not a `let` term.
    pub fn as_let(&self) -> Option<(&BindingList, &Rc<Term>)> {
        match self {
            Term::Let(b, t) => Some((b, t)),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant `true`.
    pub fn is_bool_true(&self) -> bool {
        *self == Term::Op(Operator::True, Vec::new())
    }

    /// Returns `true` if the term is the boolean constant `false`.
    pub fn is_bool_false(&self) -> bool {
        *self == Term::Op(Operator::False, Vec::new())
    }

    /// Returns `true` if the term is the given boolean constant `b`.
    pub fn is_bool_constant(&self, b: bool) -> bool {
        match b {
            true => self.is_bool_true(),
            false => self.is_bool_false(),
        }
    }
}

impl Rc<Term> {
    /// Removes a leading negation from the term, if it exists. Same thing as `match_term!((not t)
    /// = term)`.
    pub fn remove_negation(&self) -> Option<&Self> {
        match_term!((not t) = self)
    }

    /// Removes a leading negation from the term, if it exists. If it doesn't, returns a
    /// `CheckerError::TermOfWrongForm` error. Same thing as `match_term_err!((not t) = term)`.
    pub fn remove_negation_err(&self) -> Result<&Self, CheckerError> {
        match_term_err!((not t) = self)
    }

    /// Removes all leading negations from the term, and returns how many there were.
    pub fn remove_all_negations(&self) -> (u32, &Self) {
        let mut term = self;
        let mut n = 0;
        while let Some(t) = term.remove_negation() {
            term = t;
            n += 1;
        }
        (n, term)
    }

    /// Removes all leading negations from the term, and returns a boolean representing the term
    /// polarity.
    pub fn remove_all_negations_with_polarity(&self) -> (bool, &Self) {
        let (n, term) = self.remove_all_negations();
        (n % 2 == 0, term)
    }

    /// Similar to `Term::as_number`, but returns a `CheckerError` on failure.
    pub fn as_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_signed_number`, but returns a `CheckerError` on failure.
    pub fn as_signed_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_signed_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_fraction`, but returns a `CheckerError` on failure.
    pub fn as_fraction_err(&self) -> Result<Rational, CheckerError> {
        self.as_fraction()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_bool`, but returns a `CheckerError` on failure.
    pub fn as_bool_err(&self) -> Result<bool, CheckerError> {
        self.as_bool()
            .ok_or_else(|| CheckerError::ExpectedAnyBoolConstant(self.clone()))
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns a
    /// `CheckerError` if the term is not an operation term.
    pub fn as_op_err(&self) -> Result<(Operator, &[Rc<Term>]), CheckerError> {
        self.as_op()
            .ok_or_else(|| CheckerError::ExpectedOperationTerm(self.clone()))
    }

    /// Tries to unwrap a quantifier term, returning the `Binder`, the bindings and the inner term.
    /// Returns a `CheckerError` if the term is not a quantifier term.
    pub fn as_quant_err(&self) -> Result<(Binder, &BindingList, &Rc<Term>), CheckerError> {
        self.as_quant()
            .ok_or_else(|| CheckerError::ExpectedQuantifierTerm(self.clone()))
    }

    /// Tries to unwrap a binder term, returning the `Binder`, the bindings and the inner term.
    /// Returns a `CheckerError` if the term is not a binder term.
    pub fn as_binder_err(&self) -> Result<(Binder, &BindingList, &Rc<Term>), CheckerError> {
        self.as_binder()
            .ok_or_else(|| CheckerError::ExpectedBinderTerm(self.clone()))
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a `let` term.
    pub fn as_let_err(&self) -> Result<(&BindingList, &Rc<Term>), CheckerError> {
        self.as_let()
            .ok_or_else(|| CheckerError::ExpectedLetTerm(self.clone()))
    }
}

/// A constant term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    /// An integer constant term.
    Integer(Integer),

    /// A real constant term.
    Real(Rational),

    /// A string literal term.
    String(String),

    /// A bitvector literal term.
    BitVec(Integer, Integer),
}

impl Constant {
    /// Returns the sort of a constant. In case it's a `BitVec`, we only return the width.
    pub fn sort(&self) -> Sort {
        match self {
            Constant::Integer(_) => Sort::Int,
            Constant::Real(_) => Sort::Real,
            Constant::String(_) => Sort::String,
            Constant::BitVec(_, width) => Sort::BitVec(width.clone()),
        }
    }

    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Constant::Integer(i) => Some(i.clone()),
            _ => None,
        }
    }
}
