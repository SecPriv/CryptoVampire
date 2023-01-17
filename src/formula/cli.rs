use std::path::PathBuf;

use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// output location (dir or file)
    #[arg(short, long, value_name = "FILE")]
    pub output_location: PathBuf,

    /// will ouptu to a directory
    #[arg(short, long, default_value_t = false)]
    pub lemmas: bool,

    /// use rewrite in evaluate
    #[arg(long)]
    pub eval_rewrite: bool,

    /// use rewrite in crypto axioms
    #[arg(long)]
    pub crypto_rewrite: bool,

    /// use vampire's special subterm
    #[arg(long)]
    pub vampire_subterm: bool,

    /// use vampire's 'assert-theory'
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
    pub legacy_evaluate:bool,

    #[arg(long)]
    pub no_bitstring_fun:bool
}
