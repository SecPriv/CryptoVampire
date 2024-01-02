use std::path::PathBuf;

use clap::Parser;
use cryptovampire_lib::{
    container::{self, ScopedContainer},
    environement::{
        environement::{Environement, Flags, Options, RewriteFlags, SubtermFlags},
        traits::Realm,
    },
};
use utils::from_with::IntoWith;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

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
    /// NB: not in the smt standard
    #[arg(long)]
    pub vampire_subterm: bool,

    /// use vampire's 'assert-theory'
    ///
    /// NB: not in the smt standard
    #[arg(long)]
    pub assert_theory: bool,

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

    /// use `(assert (not ...))` instead of `(assert-not ...)` for the query
    /// and no `assert-ground` either
    #[arg(long)]
    pub cvc5: bool,

    /// *deprecated* use `assert-ground`
    #[arg(long)]
    pub assert_ground: bool,

    /// deactivate subterm and optimises evaluates
    ///
    /// NB: the program will crash it subterms are required somewhere
    #[arg(long, short)]
    pub no_symbolic: bool,
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
            lemmas,
            eval_rewrite,
            crypto_rewrite,
            vampire_subterm,
            assert_theory,
            skolemnise,
            preprocessing,
            legacy_evaluate,
            no_bitstring,
            cvc5,
            no_symbolic,
            assert_ground,
            ..
        } = self;
        let pure_smt = *cvc5;
        let realm = if *no_symbolic {
            Realm::Evaluated
        } else {
            Realm::Symbolic
        };

        let flags = mk_bitflag!(
            *lemmas => Flags::LEMMA,
            *assert_theory && !pure_smt => Flags::ASSERT_THEORY,
            *assert_ground && !pure_smt => Flags::ASSERT_GROUND,
            !pure_smt => Flags::ASSERT_NOT,
            *legacy_evaluate => Flags::LEGACY_EVALUATE,
            *skolemnise => Flags::SKOLEMNISE,
            *no_bitstring && realm.is_symbolic() => Flags::NO_BITSTRING
        );

        let rewrite_flags = mk_bitflag!(
            *eval_rewrite => RewriteFlags::EVALUATE,
            *crypto_rewrite => RewriteFlags::CRYPTOGRAPHY
        );

        let subterm_flags = SubtermFlags::PREPROCESS_INPUTS
            | SubtermFlags::PREPROCESS_CELLS
            | mk_bitflag!(
                *preprocessing => SubtermFlags::PREPROCESS_INSTANCES,
                *vampire_subterm && !pure_smt => SubtermFlags::VAMPIRE
            );

        Environement::new(
            container,
            realm,
            Options {
                flags,
                rewrite_flags,
                subterm_flags,
            },
        )
    }
}
