use std::path::PathBuf;

use clap::Parser;
use steel_derive::Steel;

pub use crate::input::prelude::Preludes;

/// A computationnally sound automated cryptographic protocol verifier based on the CCSA.
#[derive(Debug, Steel, Parser, Clone)]
#[steel(constructor)]
pub struct Configuration {
    /// Path to the `scheme` file
    ///
    /// defaults to stdin
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Maximal number of nodes in the egraph
    #[arg(long, default_value_t = ::golgge::Config::default().node_limit, env)]
    pub node_limit: usize,
    /// Timout for egg
    #[arg(long,
        default_value = dstr(Self::default().time_limit),
        value_parser = ::humantime::parse_duration, env)]
    pub time_limit: std::time::Duration,
    /// Iteration limit for egg
    #[arg(long, default_value_t = ::golgge::Config::default().iter_limit,env)]
    pub iter_limit: usize,

    #[arg(long,
        default_value = dstr(Self::default().vampire_timeout),
        value_parser = ::humantime::parse_duration,env)]
    pub vampire_timeout: std::time::Duration,

    /// Wether to keep the smt files around (or let the os get rid of them once
    /// we're done using them)
    #[arg(long, default_value_t=cfg!(debug_assertions), env)]
    pub keep_smt_files: bool,

    /// depth for iterative deepening
    #[arg(long, default_value_t =u64::MAX, env)]
    pub depth: u64,

    /// Choose which version of the cryptovampire prelude to include
    #[arg(long, default_value_t)]
    pub prelude_version: Preludes,

    /// don't include the cryptovampire prelude.
    ///
    /// ignore any other option
    #[arg(long)]
    pub no_cryptovampire_prelude: bool,

    /// don't include the steel prelude.
    ///
    /// ignore any other option. This will likely crash if the cryptovampire
    /// prelude is included
    #[arg(long)]
    pub no_steel_prelude: bool,

    /// number of cores used
    #[arg(long, default_value_t = Self::default().cores)]
    pub cores: u64,
}

impl Default for Configuration {
    fn default() -> Self {
        let ::golgge::Config {
            node_limit,
            time_limit,
            iter_limit,
            ..
        } = ::golgge::Config::default();
        Self {
            file: Default::default(),
            node_limit,
            time_limit,
            iter_limit,
            vampire_timeout: ::std::time::Duration::from_secs(2),
            keep_smt_files: cfg!(debug_assertions),
            depth: u64::MAX,
            prelude_version: Default::default(),
            no_cryptovampire_prelude: false,
            no_steel_prelude: false,
            cores: num_cpus::get() as u64,
        }
    }
}

fn dstr(d: ::std::time::Duration) -> &'static str {
    String::leak(humantime::format_duration(d).to_string())
}

impl Configuration {
    pub fn get_prelude(&self) -> &'static str {
        if self.no_cryptovampire_prelude {
            ""
        } else {
            self.prelude_version.get_prelude()
        }
    }
}
