use std::fmt::Display;
use std::path::PathBuf;

use serde::Serialize;

use crate::runner::RunnerResult;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Serialize)]
#[non_exhaustive]
pub enum Return {
    ToFile(PathBuf),
    AutoRun(Vec<RunnerResult>),
    Many(Vec<Self>),
}

impl Display for Return {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Return::ToFile(file) => write!(
                f,
                "wrote to the smt file to the file/directory \"{}\"",
                file.display()
            ),
            Return::AutoRun(r) => {
                write!(f, "ran automatically:")?;
                r.iter()
                    .enumerate()
                    .map(|(i, s)| (i + 1, s))
                    .try_for_each(|(i, s)| write!(f, "\n\t- protocol {i:}: {s}"))
            }
            Return::Many(m) => {
                writeln!(f, "ran many times:\n---------")?;
                m.iter()
                    .enumerate()
                    .map(|(i, s)| (i + 1, s))
                    .try_for_each(|(i, r)| write!(f, "#{i}:\n{r}"))?;
                write!(f, "\n---------")
            }
        }
    }
}
