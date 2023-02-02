use std::path::PathBuf;

use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// output location
    ///
    /// This should be a file unless `lemmas` is set
    #[arg(short, long, value_name = "FILE|DIR")]
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

    /// preprocess subterm of input
    #[arg(long, short)]
    pub input_subterm_preprocessed: bool,

    /// do as much preprocessing as possible
    #[arg(long, short)]
    pub preprocessing: bool,

    /// add (|x1| == |x1'|)/\.../\(|xn| == |xn'|) => |f(x1,...,xn)| == |f(x1',...,xn')| axioms
    #[arg(long)]
    pub legacy_evaluate: bool,

    /// remove the bitstring functions, evaluation must then be handeled by somthing else
    #[arg(long)]
    pub no_bitstring_fun: bool,

    /// use `(assert (not ...))` instead of `(assert-not ...)` for the query
    #[arg(long)]
    pub cvc5: bool,

    /// deactivate subterm and optimises evaluates
    ///
    /// NB: the program will crash it subterms are required somewhere
    #[arg(long)]
    pub no_term_algebra: bool,
}
