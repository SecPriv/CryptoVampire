use std::convert::identity;
use std::fs::File;
use std::io::Write;
use std::iter::Flatten;
use std::ops::DerefMut;
use std::sync::atomic::Ordering;

use anyhow::Context;
use cryptovampire_smt::{CVC5, SolverKind, VAMPIRE, Z3};
use parking_lot::{ArcMutexGuard, RawMutex};
use tempfile::NamedTempFile;
use utils::{econtinue_let, ereturn_let};

use crate::libraries::utils::{SmtOption, SmtSink};
use crate::runners::runner_spliter::RunnerSplitter;
use crate::runners::{Runner, SmtRunner};
use crate::{MSmt, Problem};

pub type SmtStringCache = RunnerSplitter<String>;

pub struct FileSink<'r> {
    pub cache: ArcMutexGuard<RawMutex, SmtStringCache>,
    pub files: RunnerSplitter<NamedTempFile>,
    pub runners: &'r SmtRunner,
}

impl SmtStringCache {
    pub fn clear(&mut self) {
        self.as_mut().into_iter().for_each(String::clear);
    }
}

impl<'r> FileSink<'r> {
    pub fn new(pbl: &mut Problem, runners: &'r SmtRunner) -> Self {
        let cache = pbl
            .cache
            .smt
            .string_cache
            .try_lock_arc()
            .expect("no concurent write to the cache");

        let files = cache
            .names()
            .map(|solver| {
                tempfile::Builder::new()
                    .prefix(&format!("cryptovampire-{solver}-"))
                    .suffix(".smt")
                    .disable_cleanup(pbl.config.keep_smt_files)
                    .tempfile()
            })
            .transpose()
            .unwrap();

        Self {
            cache,
            files,
            runners,
        }
    }
}

impl<'a, 'r> SmtSink<'a> for FileSink<'r> {
    fn extend_smt(&mut self, pbl: &Problem, opts: &SmtOption, iter: utils::implvec!(MSmt<'a>)) {
        let Self {
            cache,
            files,
            runners,
        } = self;
        let nasserts = &pbl.cache.smt.nassert;

        for command in iter {
            let comment = command
                .is_any_assert()
                .then(|| format!(";; {}\n", nasserts.fetch_add(1, Ordering::AcqRel)));
            let cmd = &command;
            let comment = comment.as_deref();

            mwrite(opts, cmd, comment, files, cache, &runners.vampire).unwrap()
        }
    }

    fn reserve(&mut self, _: usize) {}
}

fn mwrite<'a, R: Runner>(
    options: &SmtOption,
    command: &MSmt<'a>,
    comment: Option<&str>,
    files: &mut RunnerSplitter<NamedTempFile>,
    cache: &mut SmtStringCache,
    runner: &Option<R>,
) -> anyhow::Result<()> {
    ereturn_let!(let Some(runner) = runner.as_ref(), Ok(()));
    let file = runner.mut_splitter(files).unwrap();
    let kind = runner.get_sover_kind();
    let cmd = command
        .convert(kind)
        .with_context(|| format!("converting {command}"))?;

    cmd.check(kind).with_context(|| format!("check {cmd}"))?;

    let mut str = String::new();

    if let Some(comment) = comment {
        str.push_str(comment);
    }
    {
        use ::std::fmt::Write;
        writeln!(&mut str, "{cmd}")?;
    }

    if options.depend_on_context {
        runner
            .mut_splitter(cache)
            .expect("caches should be consistent")
            .push_str(&str);
    }
    {
        use ::std::io::Write;
        write!(file, "{str}")?
    }
    Ok(())
}
