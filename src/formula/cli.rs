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
    pub skolemnise: bool
}
