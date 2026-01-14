use std::fmt::Debug;

use bon::bon;
use itertools::Itertools;
use utils::implvec;

use crate::problem::publish::NoncePublicSearchState;
use crate::protocol::Protocol;
use crate::terms::{CryptographicAssumption, Formula, Function, FunctionCollection, Rewrite};
use crate::{Configuration, MSmt};

mod analysis;
pub(crate) use analysis::CVRuleTrait;
pub use analysis::{PAnalysis, PRule, RcRule};

mod state;
pub use state::ProblemState;

mod constrainst;
pub use constrainst::{BoundStep, ConstrainOp, Constrains};

declare_trace!($"problem");

mod cryptography;
mod formulas;
mod protocol;
mod run;

mod functions;
pub use functions::FunctionBuilder;

mod report;
pub use report::Report;

mod checkpoint;

mod publish;
pub use publish::PublicTerm;

/// A problem for the solver to solve
///
/// This struct contains all the information needed to run the solver.
/// It contains the protocols to prove indistinguishability on, the functions,
/// the cryptographic assumptions, and the extra rules, rewrites, and SMT formulas.
#[non_exhaustive]
pub struct Problem {
    /// The configuration (e.g., cli arguments and such)
    pub config: Configuration,
    /// The protocols we want to prove indistiguishability on
    ///
    /// The vector must be at least 2 long
    protocols: Vec<Protocol>,
    /// The functions
    function: FunctionCollection,

    /// The cryptographic assumptions
    pub(crate) cryptography: Vec<CryptographicAssumption>,

    /// Extra rules to add to the solver
    extra_rules: Vec<RcRule>,
    /// Extra rewrites to add to the solver
    extra_rewrite: Vec<Rewrite>,
    /// Extra SMT formulas to add to the solver
    extra_smt: Vec<MSmt>,

    /// cache for the smt prelude
    smt_prelude: Option<Vec<MSmt>>,

    /// the current step in the run (if any)
    current_step: Option<CurrentStep>,

    /// a cache for the quantifiers
    quantifier_cache: Vec<(Formula, Function)>,

    pub state: ProblemState,

    constrains: Vec<Constrains>,

    pub report: Report,

    /// Terms that are "public"
    public_terms: Vec<PublicTerm>,

    nonce_finder: NoncePublicSearchState,
}

/// Represents the current step in the execution of the problem
#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct CurrentStep {
    /// The index of the current step in the problem.
    pub idx: usize,
    /// Specific arguments given for this run. All the [Function]s are constants.
    pub args: Vec<Function>,
}

impl Problem {
    /// Checks if the protocols are compatible
    ///
    /// This function checks that all the protocols are compatible with each other.
    /// Two protocols are compatible if they have the same steps and the same
    /// variables in each step.
    pub fn valid(&self) -> bool {
        self.protocols
            .iter()
            .tuple_windows()
            .all(|(a, b)| Protocol::are_compatible(a, b))
    }
}

#[bon]
impl Problem {
    /// Creates a new `Problem` instance with the specified components.
    ///
    /// This is typically used with the `ProblemBuilder` for a more ergonomic construction.
    #[builder(builder_type = ProblemBuilder)]
    pub fn new(
        #[builder(field = Self::default_cryptography())] cryptography: Vec<CryptographicAssumption>,
        #[builder(field = None)] smt_prelude: Option<Vec<MSmt>>,
        /// The configuration (e.g., cli arguments and such)
        #[builder(default)]
        config: Configuration,
        /// The protocol we want to prove indistiguishability on
        ///
        /// The vector must be at least 2 long
        #[builder(with = <_>::from_iter, default = vec![])]
        protocols: Vec<Protocol>,
        /// The constrains on the steps
        #[builder(with = <_>::from_iter, default = vec![])]
        constrains: Vec<Constrains>,
        /// The functions
        #[builder(default = FunctionCollection::init())]
        function: FunctionCollection,

        #[builder(with = <_>::from_iter, default = vec![])] extra_rules: Vec<RcRule>,
        #[builder(with = <_>::from_iter, default = vec![])] extra_rewrite: Vec<Rewrite>,
        #[builder(with = <_>::from_iter, default = vec![])] extra_smt: Vec<MSmt>,
    ) -> Self {
        Self {
            config,
            protocols,
            function,
            cryptography,
            extra_rules,
            extra_rewrite,
            extra_smt,
            smt_prelude,
            current_step: None,
            quantifier_cache: vec![],
            state: Default::default(),
            constrains,
            report: Default::default(),
            public_terms: Default::default(),
            nonce_finder: Default::default(),
        }
    }
}

impl<S> ProblemBuilder<S>
where
    S: problem_builder::State,
{
    /// removes the default cryptography
    pub fn reset_cryptograhy(mut self) -> Self {
        self.cryptography.clear();
        self
    }

    /// extends the cryptography with the given assumptions
    pub fn extend_cryptography(mut self, crypto: implvec!(CryptographicAssumption)) -> Self {
        self.cryptography.extend(crypto);
        self
    }
}

impl Default for Problem {
    /// Creates a new `Problem` with default values.
    fn default() -> Self {
        Self::builder().build()
    }
}

impl Debug for Problem {
    /// Formats the `Problem` for debugging purposes.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Problem")
            .field("config", &self.config)
            .field("protocols", &self.protocols)
            .field("function", &self.function)
            .field(
                "extra_rules",
                &self
                    .extra_rules
                    .iter()
                    // .map(|x| golgge::DebugRule::new(x.as_ref()))
                    .collect_vec(),
            )
            .field("extra_rewrite", &self.extra_rewrite)
            .field("extra_smt", &self.extra_smt)
            .finish()
    }
}
