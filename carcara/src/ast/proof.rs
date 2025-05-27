use super::{ProofIter, Rc, SortedVar, Term};

/// A proof in the Alethe format.
#[derive(Debug, Default, Clone)]
pub struct Proof {
    /// The constants defined in the proof using `define-fun` with arity zero.
    ///
    /// This is only used to reconstruct these `define-fun`s when printing the proof.
    pub constant_definitions: Vec<(String, Rc<Term>)>,

    /// The proof commands.
    pub commands: Vec<ProofCommand>,
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
    pub args: Vec<Rc<Term>>,

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

    /// The arguments of the subproof.
    ///
    /// They can be either a variable declaration, of the form `(<symbol> <sort>)`, or an
    /// assignment, of the form `(:= <symbol> <term>)`.
    pub args: Vec<AnchorArg>,

    /// Subproof id used for context hashing purposes.
    pub context_id: usize,
}

/// An argument for an `anchor` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnchorArg {
    /// A "variable declaration" style argument, of the form `(<symbol> <sort>)`.
    Variable(SortedVar),

    /// An "assignment" style argument, of the form `(:= (<symbol> <sort>) <term>)`.
    Assign(SortedVar, Rc<Term>),
}

impl Proof {
    /// Returns an iterator over the proof commands. See [`ProofIter`].
    pub fn iter(&self) -> ProofIter {
        ProofIter::new(&self.commands)
    }
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

    /// Returns a string with the rule of this command.
    ///
    /// For subproofs, this is the rule of the last step in the subproof.
    /// For assumes, return "assume"
    pub fn rule(&self) -> &str {
        match self {
            ProofCommand::Assume { .. } => "assume",
            ProofCommand::Step(s) => &s.rule,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().rule(),
        }
    }

    /// Returns a reference for a vector with the args of this command.
    ///
    /// For subproofs, this is the args of the last step in the subproof.
    /// For assumes, return reference to an empty vector
    pub fn args(&self) -> &Vec<Rc<Term>> {
        match self {
            ProofCommand::Assume { .. } => {
                static NO_ARGS: Vec<Rc<Term>> = Vec::new();
                &NO_ARGS
            }
            ProofCommand::Step(s) => &s.args,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().args(),
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
    
    /// Returns a reference for a vector with the premises of this command.
    ///
    /// For subproofs, this is the premises of the last step in the subproof
    /// (that is guaranteed to not have any command native to the subproof).
    /// For assumes, return reference to an empty vector
    pub fn premises(&self) -> &Vec<(usize,usize)> {
        match self {
            ProofCommand::Assume { .. } => {
                static NO_PREM: Vec<(usize,usize)> = Vec::new();
                &NO_PREM
            }
            ProofCommand::Step(s) => &s.premises,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().premises(),
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

    /// Returns `true` if the command rule is `resolution` or `th-resolution`.
    pub fn is_resolution(&self) -> bool {
        self.rule() == "resolution" || self.rule() == "th-resolution"
    }
}

impl Subproof {
    pub fn new_placeholder(&self, context_id: usize) -> Self {
        let conclusion = self.commands.last().unwrap().clone();
        Subproof {
            context_id,
            args: vec![],
            commands: vec![conclusion],
        }
    }
}

impl AnchorArg {
    /// Returns `Some` if the anchor arg is a "variable" style argument.
    pub fn as_variable(&self) -> Option<&SortedVar> {
        match self {
            AnchorArg::Variable(v) => Some(v),
            AnchorArg::Assign(_, _) => None,
        }
    }

    /// Returns `true` if the anchor arg is a "variable" style argument.
    pub fn is_variable(&self) -> bool {
        matches!(self, Self::Variable(_))
    }

    /// Returns `Some` if the anchor arg is an "assignment" style argument.
    pub fn as_assign(&self) -> Option<(&String, &Rc<Term>)> {
        match self {
            AnchorArg::Variable(_) => None,
            AnchorArg::Assign((name, _), value) => Some((name, value)),
        }
    }

    /// Returns `true` if the anchor arg is an "assignment" style argument.
    pub fn is_assign(&self) -> bool {
        matches!(self, Self::Assign(..))
    }
}
