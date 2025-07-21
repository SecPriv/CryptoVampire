use egg::{Analysis, Language, Runner};

mod rule;
pub use rule::{DebugRule, Dependancy, Fresh, PrologRule, Rule};

mod simplify_and;
pub use simplify_and::{WithAnd, WithTrue, and_simpl_rewrite};

mod weight;
pub use weight::MWeight;

mod analysis;
pub use analysis::{MAnalysis, WeightedAnalysis};

pub use program::Program;
mod program;

mod proof;
pub use proof::ProofItem;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Config {
    pub iter_limit: usize,
    pub node_limit: usize,
    pub time_limit: std::time::Duration,
    pub trace_prolog: bool,
}

impl Config {
    pub fn apply<L: Language, N: Analysis<L>>(&self, runner: Runner<L, N>) -> Runner<L, N> {
        runner
            .with_iter_limit(self.iter_limit)
            .with_node_limit(self.node_limit)
            .with_time_limit(self.time_limit)
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            iter_limit: 150,
            node_limit: 500,
            time_limit: std::time::Duration::from_secs(5),
            trace_prolog: cfg!(debug_assertions),
        }
    }
}
