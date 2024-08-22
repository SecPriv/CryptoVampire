use std::{
    fmt::Display,
    path::{Path, PathBuf},
};

use clap::{Parser, Subcommand};
use cryptovampire_lib::{
    container::ScopedContainer,
    environement::{
        environement::{
            EnabledSolvers, Environement, Flags, Locations, Options, RewriteFlags, SolverConfig,
            SubtermFlags,
        },
        traits::Realm,
    },
};
use utils::from_with::IntoWith;

#[derive(Parser, Debug, Clone)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// use rewrite in evaluate
    ///
    /// NB: not in the smt standard
    #[arg(long)]
    pub eval_rewrite: bool,

    /// use rewrite in crypto axioms
    ///
    /// NB: not in the smt standard
    #[arg(long)]
    pub crypto_rewrite: bool,

    /// use vampire's special subterm
    ///
    /// NB: not in the smt standard, requires modified vampire
    #[arg(long)]
    pub vampire_subterm: bool,

    /// skolemnise before passing to sat solver
    #[arg(long, short)]
    pub skolemnise: bool,

    // this is now activated by default
    /// preprocess subterm of input
    // #[arg(long, short)]
    // pub input_subterm_preprocessed: bool,

    /// do as much preprocessing as possible
    #[arg(long, short)]
    pub preprocessing: bool,

    /// add (|x1| == |x1'|)/\.../\(|xn| == |xn'|) => |f(x1,...,xn)| == |f(x1',...,xn')| axioms
    #[arg(long)]
    pub legacy_evaluate: bool,

    /// remove the bitstring functions, evaluation must then be handeled by somthing else
    #[arg(long)]
    pub no_bitstring: bool,

    /// deactivate subterm and optimises evaluates
    ///
    /// NB: the program will crash it subterms are required somewhere
    #[arg(long, short)]
    pub no_symbolic: bool,

    /// What should the input format be?
    #[arg(long, default_value_t = Input::Cryptovampire)]
    pub input_format: Input,

    /// Defaults to `auto`
    #[command(subcommand)]
    pub command: Option<Command>,
}

#[derive(Subcommand, Debug, Clone)]
pub enum Command {
    Auto(Auto),
    ToFile(ToFile),
}

impl Default for Command {
    fn default() -> Self {
        Self::Auto(Default::default())
    }
}

#[derive(clap::Args, Debug, Clone)]
pub struct ToFile {
    /// output location
    ///
    /// This should be a file unless `lemmas` is set
    #[arg(short, long, value_name = "FILE|DIR", default_value = "/dev/stdout")]
    pub output_location: PathBuf,

    /// uses the lemmas
    ///
    /// It will generate multiples files
    ///     lemma_0: output_location/0.smt
    ///     ...
    ///     lemma_n: output_location/n.smt
    ///     query: output_location/n+1.smt
    ///
    /// The order of the lemma is determined based on their order in the file.
    /// The files are generated such that lemma_0 to n are assertion in lemma_n+1's
    /// file. Same for the query
    #[arg(short, long, default_value_t = false)]
    pub lemmas: bool,

    /// use vampire's 'assert-theory'
    ///
    /// NB: not in the smt standard, requires vampire
    #[arg(long)]
    pub assert_theory: bool,

    /// use `(assert (not ...))` instead of `(assert-not ...)` for the query
    /// and no `assert-ground` either
    #[arg(long)]
    pub cvc5: bool,

    /// *deprecated* use vampire's `assert-ground`. Requires modified vampire
    #[arg(long)]
    pub assert_ground: bool,
}

#[derive(clap::Args, Debug, Clone)]
pub struct Auto {
    /// uses the lemmas
    ///
    /// It will generate multiples files
    ///     lemma_0: output_location/0.smt
    ///     ...
    ///     lemma_n: output_location/n.smt
    ///     query: output_location/n+1.smt
    ///
    /// The order of the lemma is determined based on their order in the file.
    /// The files are generated such that lemma_0 to n are assertion in lemma_n+1's
    /// file. Same for the query
    #[arg(short, long, default_value_t = false)]
    pub lemmas: bool,

    /// Upper bound of how many tries on the vampire runner
    ///
    /// 0 for an infinite number of tries
    #[arg(long, default_value = "5")]
    pub num_of_retry: u32,

    /// Vampire execution time
    #[arg(long, default_value = "1")]
    pub timeout: f64,

    /// A folder to put temporary smt files
    #[arg(long, value_name = "DIR")]
    pub solver_file_debug: Option<PathBuf>,

    /// Deactivate the lemmas.
    ///
    /// CryptoVampire will ignore the lemmas as a whole and work as if there weren't any. This is used for testing purposes.
    #[arg(long)]
    pub ignore_lemmas: bool,

    /// Location of the `vampire` executable
    #[arg(long, default_value = "vampire", value_name = "EXE_FILE")]
    pub vampire_location: PathBuf,

    /// Location of the `z3` executable
    #[arg(long, default_value = "z3", value_name = "EXE_FILE")]
    pub z3_location: PathBuf,

    /// Location of the `cvc5` executable
    #[arg(long, default_value = "cvc5", value_name = "EXE_FILE")]
    pub cvc5_location: PathBuf,

    #[arg(long)]
    pub disable_vampire: bool,

    #[arg(long)]
    pub disable_z3: bool,

    #[arg(long)]
    pub disable_cvc5: bool,
}

#[derive(clap::ValueEnum, Clone, Default, Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Input {
    /// use a cryptovampire file
    #[default]
    Cryptovampire,

    /// use a json file produced by squirrel using the `cryptovampire` tactic
    ///
    /// https://github.com/squirrel-prover/squirrel-prover/
    SquirrelJSON,
}

impl Input {
    /// Returns `true` if the input is [`Cryptovampire`].
    ///
    /// [`Cryptovampire`]: Input::Cryptovampire
    #[must_use]
    pub fn is_cryptovampire(&self) -> bool {
        matches!(self, Self::Cryptovampire)
    }

    /// Returns `true` if the input is [`SquirrelJSON`].
    ///
    /// [`SquirrelJSON`]: Input::SquirrelJSON
    #[must_use]
    pub fn is_squirrel_json(&self) -> bool {
        matches!(self, Self::SquirrelJSON)
    }
}

impl Display for Input {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cryptovampire => write!(f, "cryptovampire"),
            Self::SquirrelJSON => write!(f, "squirrel-json"),
        }
    }
}

impl Default for Auto {
    fn default() -> Self {
        Self {
            lemmas: true,
            num_of_retry: 5,
            timeout: 1.0,
            solver_file_debug: None,
            ignore_lemmas: false,
            vampire_location: "vampire".into(),
            z3_location: "z3".into(),
            cvc5_location: "cvc5".into(),
            disable_vampire: false,
            disable_z3: false,
            disable_cvc5: false,
        }
    }
}

macro_rules! mk_bitflag {
    ($bool:expr => $flag:expr) => {
        if $bool {
            $flag
        } else {
            Default::default()
        }
    };

    ($($bool:expr => $flag:expr),+ $(,)?) => {
        $(mk_bitflag!($bool => $flag))|+
    };
}

impl<'bump> IntoWith<Environement<'bump>, &'bump ScopedContainer<'bump>> for &Args {
    fn into_with(self, container: &'bump ScopedContainer<'bump>) -> Environement<'bump> {
        let Args {
            eval_rewrite,
            crypto_rewrite,
            vampire_subterm,
            skolemnise,
            preprocessing,
            legacy_evaluate,
            no_bitstring,
            no_symbolic,
            command,
            ..
        } = self;
        let tmp = Default::default();
        let command = command.as_ref().unwrap_or(&tmp);
        let realm = if *no_symbolic {
            Realm::Evaluated
        } else {
            Realm::Symbolic
        };

        let mut flags = mk_bitflag!(
            // *lemmas => Flags::LEMMA,
            // *assert_theory && !pure_smt => Flags::ASSERT_THEORY,
            // *assert_ground && !pure_smt => Flags::ASSERT_GROUND,
            // !pure_smt => Flags::ASSERT_NOT,
            *legacy_evaluate => Flags::LEGACY_EVALUATE,
            *skolemnise => Flags::SKOLEMNISE,
            *no_bitstring && realm.is_symbolic() => Flags::NO_BITSTRING,
            // *ignore_lemmas => Flags::IGNORE_LEMMAS
        );

        let rewrite_flags = mk_bitflag!(
            *eval_rewrite => RewriteFlags::EVALUATE,
            *crypto_rewrite => RewriteFlags::CRYPTOGRAPHY
        );

        let mut subterm_flags = SubtermFlags::PREPROCESS_INPUTS
            | SubtermFlags::PREPROCESS_CELLS
            | mk_bitflag!(
                *preprocessing => SubtermFlags::PREPROCESS_INSTANCES,
                *vampire_subterm  => SubtermFlags::VAMPIRE
            );
        let solver_configuration = match command {
            Command::Auto(
                a @ Auto {
                    lemmas,
                    ignore_lemmas,
                    ..
                },
            ) => {
                flags |= mk_bitflag!(
                    *lemmas && !*ignore_lemmas => Flags::LEMMA,
                    *ignore_lemmas => Flags::IGNORE_LEMMAS
                );
                a.clone().into()
            }
            Command::ToFile(ToFile {
                output_location: _,
                lemmas,
                assert_theory,
                cvc5,
                assert_ground,
            }) => {
                flags |= mk_bitflag!(
                    *lemmas => Flags::LEMMA,
                    *assert_theory=> Flags::ASSERT_THEORY,
                    *assert_ground => Flags::ASSERT_GROUND,
                );
                if *cvc5 {
                    flags -= Flags::ASSERT_GROUND | Flags::ASSERT_NOT | Flags::ASSERT_THEORY;
                    subterm_flags -= SubtermFlags::VAMPIRE;
                }
                SolverConfig {
                    enable_solvers: EnabledSolvers::empty(),
                    ..Auto::default().into()
                }
            }
        };

        Environement::new(
            container,
            realm,
            Options {
                flags,
                rewrite_flags,
                subterm_flags,
            },
            solver_configuration,
        )
    }
}

impl Into<SolverConfig> for Auto {
    fn into(self) -> SolverConfig {
        let Auto {
            num_of_retry,
            timeout,
            solver_file_debug,
            vampire_location,
            z3_location,
            cvc5_location,
            disable_vampire,
            disable_z3,
            disable_cvc5,
            ..
        } = self;
        let locations = Locations {
            vampire: vampire_location,
            z3: z3_location,
            cvc5: cvc5_location,
        };

        let enable_solvers = {
            let mut flags = EnabledSolvers::empty();
            if !disable_vampire {
                flags |= EnabledSolvers::VAMPIRE
            }
            if !disable_z3 {
                flags |= EnabledSolvers::Z3
            }
            if !disable_cvc5 {
                flags |= EnabledSolvers::CVC5
            }
            flags
        };

        SolverConfig {
            locations,
            enable_solvers,
            num_of_retry,
            timeout,
            smt_debug: solver_file_debug,
        }
    }
}

impl Args {
    pub fn get_output_location(&self) -> Option<&Path> {
        match &self.command {
            Some(Command::ToFile(ToFile {
                output_location, ..
            })) => Some(output_location.as_path()),
            _ => None,
        }
    }
    pub fn get_mut_output_location(&mut self) -> Option<&mut PathBuf> {
        match &mut self.command {
            Some(Command::ToFile(ToFile {
                ref mut output_location,
                ..
            })) => Some(output_location),
            _ => None,
        }
    }
}
