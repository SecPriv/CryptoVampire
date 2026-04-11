use std::path::PathBuf;

use clap::{Parser, Subcommand};
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

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

    /// activate golgge trace for goals
    #[arg(long, short('T'), env)]
    pub trace: bool,

    /// activate golgge trace for rebuilds
    #[arg(long)]
    pub trace_rebuilds: bool,

    /// follow to set of nonce currently "published"
    #[arg(long)]
    pub trace_guessed_published_nonces: bool,

    #[arg(long,
        short('t'),
        default_value = dstr(Self::default().smt_timeout),
        value_parser = ::humantime::parse_duration, env)]
    pub smt_timeout: std::time::Duration,

    /// number of cores used
    /// 
    /// This will be distributed among the smt solvers
    #[arg(long, short('c'), default_value_t = Self::default().cores)]
    pub cores: u64,

    /// Wether to keep the smt files around (or let the os get rid of them once
    /// we're done using them)
    #[arg(long, short('k'), default_value_t=cfg!(debug_assertions), env)]
    pub keep_smt_files: bool,

    /// Timout for egg
    #[arg(long,
        default_value = dstr(Self::default().egg_timeout),
        value_parser = ::humantime::parse_duration, env)]
    pub egg_timeout: std::time::Duration,

    /// Maximal number of nodes in the egraph
    #[arg(long, default_value_t = Self::default().egg_node_limit, env)]
    pub egg_node_limit: usize,

    /// Iteration limit for egg
    #[arg(long, default_value_t = Self::default().egg_iter_limit,env)]
    pub egg_iter_limit: usize,

    /// depth for iterative deepening
    /// 
    /// This can mess with caching. It is recommended to leave it to its default value of `u64::MAX`.
    #[arg(long, default_value_t =u64::MAX, env)]
    pub depth: u64,

    /// don't include the steel prelude.
    ///
    /// ignore any other option. This will likely crash if the cryptovampire
    /// prelude is included
    #[arg(long)]
    pub no_steel_prelude: bool,

    /// Guided search for publishable nonce
    ///
    /// The proof sometimes requires to "publish" messages that should be secret
    /// by the protocol specification. This features does a guided brute force
    /// search to find such nonces.
    #[arg(long)]
    pub guided_nonce_search: bool,

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

    /// Enable if commute rewrite rules (not recommended)
    #[arg(long)]
    pub if_commute: bool,

    /// Add various `and` related rewrite rules (not recommended)
    ///
    /// This makes the search more complete, but exponentially increases the
    /// complexity
    #[arg(long)]
    pub complete_and: bool,

    /// Propagate to `vampire` `--forced_options`
    ///
    /// Options in the format `<opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN>`
    /// that override the option values set by other means (also inside
    /// portfolio mode strategies)
    #[arg(long, env)]
    pub vampire_forced_option: Option<String>,

    /// Path to `vampire` executable
    /// 
    /// Unless disable, will default to looking in the `PATH`
    #[arg(long, env, group = "vampire")]
    pub vampire_path: Option<PathBuf>,

    /// Path to `z3` executable
    /// 
    /// Unless disable, will default to looking in the `PATH`
    #[arg(long, env, group = "z3")]
    pub z3_path: Option<PathBuf>,

    /// Path to `cvc5` executable
    /// 
    /// Unless disable, will default to looking in the `PATH`
    #[arg(long, env, group = "cvc5")]
    pub cvc5_path: Option<PathBuf>,

    #[arg(long, env, group = "vampire")]
    pub disable_vampire: bool,

    #[arg(long, env, group = "z3")]
    pub disable_z3: bool,

    #[arg(long, env, group = "cvc5")]
    pub disable_cvc5: bool,
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
            egg_node_limit: NODE_LIMIT_DEFAULT,
            egg_timeout: time_limit,
            egg_iter_limit: iter_limit,
            smt_timeout: ::std::time::Duration::from_secs(2),
            keep_smt_files: cfg!(debug_assertions),
            depth: u64::MAX,
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
            trace_guessed_published_nonces: false,
            vampire_forced_option: None,
            vampire_path: None,
            z3_path: None,
            cvc5_path: None,
            disable_vampire: false,
            disable_z3: false,
            disable_cvc5: false,
        }
    }
}

impl Configuration {
    pub fn from_cli() -> Self {
        use ::std::mem::take;
        let mut init = Configuration::parse();

        // sets to false at the same time
        if !take(&mut init.disable_vampire) && init.vampire_path.is_none() {
            init.vampire_path = which::which("vampire").ok()
        }

        // sets to false at the same time
        if !take(&mut init.disable_z3) && init.z3_path.is_none() {
            init.z3_path = which::which("z3").ok()
        }

        // sets to false at the same time
        if !take(&mut init.disable_cvc5) && init.cvc5_path.is_none() {
            init.cvc5_path = which::which("cvc5").ok()
        }


        init
    }
}

fn dstr(d: ::std::time::Duration) -> &'static str {
    String::leak(humantime::format_duration(d).to_string())
}
