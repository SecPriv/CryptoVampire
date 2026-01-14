use std::path::PathBuf;

use clap::{Parser, Subcommand};
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
pub use crate::input::prelude::Preludes;

#[derive(Debug, Steel, Clone, Subcommand, Default)]
pub enum Commands {
    /// Uses Steel's repl mode
    Repl,
    /// Reads from a file
    File {
        /// Path to the `scheme` file
        ///
        /// defaults to stdin
        #[arg(value_name = "FILE")]
        file: PathBuf,
    },
    /// Reads from stdin (default)
    #[default]
    Stdin,
}

/// A computationnally sound automated cryptographic protocol verifier based on the CCSA.
///
/// NB: the command line interface is unstable
#[derive(Debug, Steel, Parser, Clone)]
#[command(version, about, long_about = None)]
#[command(propagate_version = true)]
pub struct Configuration {
    /// Default to reading a scheme file from stdin
    #[command(subcommand)]
    pub command: Option<Commands>,

    /// Maximal number of nodes in the egraph
    #[arg(long, default_value_t = Self::default().node_limit, env)]
    pub node_limit: usize,
    /// Timout for egg
    #[arg(long,
        default_value = dstr(Self::default().time_limit),
        value_parser = ::humantime::parse_duration, env)]
    pub time_limit: std::time::Duration,
    /// Iteration limit for egg
    #[arg(long, default_value_t = Self::default().iter_limit,env)]
    pub iter_limit: usize,

    #[arg(long,
        short('t'),
        default_value = dstr(Self::default().vampire_timeout),
        value_parser = ::humantime::parse_duration, env)]
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
    #[arg(long, short('c'), default_value_t = Self::default().cores)]
    pub cores: u64,

    /// Limit on how many new nonce 'prf' can generate
    ///
    /// This might be helpful to avoid loops
    #[arg(long, default_value_t = Self::default().prf_limit)]
    pub prf_limit: usize,

    /// Fa limits
    ///
    /// Note: increasing this limit nastily increases the complexity of the
    /// problem. A lot of heuristics are put in place to keep this as low as
    /// possible. Only increase this if you know what you are doing (and have a
    /// *lot* of time to lose)
    #[arg(long, default_value_t = Self::default().fa_limit)]
    pub fa_limit: usize,

    /// Limit on how many new nonce 'enc-kp' can generate
    ///
    /// This might be helpful to avoid loops
    #[arg(long, default_value_t = Self::default().enc_kp_limit)]
    pub enc_kp_limit: usize,

    #[arg(long, default_value_t = Self::default().ddh_limit)]
    pub ddh_limit: usize,

    /// activate golgge trace for goals
    #[arg(long, short('T'))]
    pub trace: bool,

    /// activate golgge trace for rebuilds
    #[arg(long)]
    pub trace_rebuilds: bool,

    /// Enable if commute rewrite rules
    #[arg(long)]
    pub if_commute: bool,

    /// Add various `and` related rewrite rules
    ///
    /// This makes the search more complete, but exponentially increases the
    /// complexity
    #[arg(long)]
    pub complete_and: bool,

    /// Guided search for publishable nonce
    ///
    /// The proof sometimes requires to "publish" messages that should be secret
    /// by the protocol specification. This features does a guided brute force
    /// search to find such nonces.
    #[arg(long)]
    pub guided_nonce_search: bool,
}

static NODE_LIMIT_DEFAULT: usize = 100000;
static NONCE_GENERATION_DEFAULT: usize = 3;

impl Default for Configuration {
    /// Returns a default `Configuration` instance.
    fn default() -> Self {
        let ::golgge::Config {
            time_limit,
            iter_limit,
            ..
        } = ::golgge::Config::default();
        Self {
            // file: Default::default(),
            command: None,
            node_limit: NODE_LIMIT_DEFAULT,
            time_limit,
            iter_limit,
            vampire_timeout: ::std::time::Duration::from_secs(2),
            keep_smt_files: cfg!(debug_assertions),
            depth: u64::MAX,
            prelude_version: Default::default(),
            no_cryptovampire_prelude: false,
            no_steel_prelude: false,
            cores: num_cpus::get() as u64,
            fa_limit: 4,
            enc_kp_limit: NONCE_GENERATION_DEFAULT,
            prf_limit: NONCE_GENERATION_DEFAULT,
            trace: cfg!(debug_assertions),
            trace_rebuilds: false,
            if_commute: false,
            complete_and: false,
            ddh_limit: NONCE_GENERATION_DEFAULT,
            guided_nonce_search: false,
        }
    }
}

fn dstr(d: ::std::time::Duration) -> &'static str {
    String::leak(humantime::format_duration(d).to_string())
}

impl Configuration {
    /// Returns the appropriate prelude content based on the configuration.
    pub fn get_prelude(&self) -> &'static str {
        if self.no_cryptovampire_prelude {
            ""
        } else {
            self.prelude_version.get_prelude()
        }
    }
}

impl Registerable for Configuration {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        module.register_fn("vampire-timeout", |x: Self| x.vampire_timeout)
    }
}
