use bitflags::bitflags;
use bon::Builder;
use egg::{Analysis, EGraph, Id, Language, Runner};
use serde::{Deserialize, Serialize};

bitflags! {
  #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
       Hash, Debug, Serialize, Deserialize)]
  pub struct DebugLevel: u32 {
    const RULE = 1 << 0;
    const REBUILDS = 1 << 1;
    const OTHER = 1 << 2;
    const ID_UPDATES = 1 << 3;
  }
}

bitflags! {
  #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
       Hash, Debug, Serialize, Deserialize)]
  pub struct Flags: u8 {
    /// Enable Memoization (activated by default)
    ///
    /// This caches successes *and* faillure. Incompatible with
    /// [Self::DEPTH_LIMIT]
    const MEMOIZATION = 1 << 0;
    /// Enable depth limit (disabled by default)
    ///
    /// Not very sound with memoization enabled
    const DEPTH_LIMIT = 1 << 1;
  }
}

impl Default for DebugLevel {
    fn default() -> Self {
        if cfg!(debug_assertions) {
            DebugLevel::RULE | DebugLevel::ID_UPDATES
        } else {
            DebugLevel::empty()
        }
    }
}

/// Configuration for the Golgge e-graph runner.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
#[non_exhaustive]
pub struct Config {
    #[builder(default = Config::default().iter_limit)]
    pub iter_limit: usize,
    #[builder(default = Config::default().node_limit)]
    pub node_limit: usize,
    #[builder(default = Config::default().time_limit)]
    pub time_limit: std::time::Duration,
    #[builder(default = Config::default().trace)]
    pub trace: DebugLevel,
    #[builder(default = Config::default().flags)]
    pub flags: Flags,
}

impl Config {
    /// Applies the configuration settings to an `egg::Runner`.
    pub fn apply<L: Language, N: Analysis<L>>(&self, runner: Runner<L, N>) -> Runner<L, N> {
        runner
            .with_iter_limit(self.iter_limit)
            .with_node_limit(self.node_limit)
            .with_time_limit(self.time_limit)
    }
}

impl Default for Config {
    /// Returns a default `Config` instance.
    fn default() -> Self {
        Self {
            iter_limit: 150,
            node_limit: 500,
            time_limit: std::time::Duration::from_secs(5),
            trace: DebugLevel::default(),
            flags: Default::default(),
        }
    }
}

impl Default for Flags {
    fn default() -> Self {
        Self::MEMOIZATION
    }
}
