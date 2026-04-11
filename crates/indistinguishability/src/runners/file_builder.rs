use std::any;
use std::convert::identity;
use std::fs::File;
use std::io::Write;
use std::iter::Flatten;
use std::num::NonZeroU32;
use std::ops::DerefMut;
use std::path::Path;
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

#[derive(Debug)]
pub struct CachedFile {
    file: NamedTempFile,
    cache: String,
}

pub struct FileSink<'r> {
    pub files: RunnerSplitter<CachedFile>,
    pub nasserts: NonZeroU32,
    pub runners: &'r SmtRunner,
}

impl SmtStringCache {
    pub fn clear(&mut self) {
        self.as_mut().into_iter().for_each(String::clear);
    }
}

impl CachedFile {
    pub fn new(name: &str, pbl: &Problem) -> anyhow::Result<Self> {
        let file = mk_temp_file(name, pbl)?;
        Ok(Self {
            file,
            cache: String::new(),
        })
    }

    pub fn write_cache(&mut self) -> ::std::io::Result<()> {
        let CachedFile { file, cache } = self;
        write!(file, "{cache}")
    }

    pub fn path(&self) -> &Path {
        self.file.path()
    }
}

fn mk_temp_file(name: &str, pbl: &Problem) -> ::std::io::Result<NamedTempFile> {
    tempfile::Builder::new()
        .prefix(&format!("cryptovampire-{name}-"))
        .suffix(".smt")
        .disable_cleanup(pbl.config.keep_smt_files)
        .tempfile()
}

impl<'r> FileSink<'r> {
    pub fn new(pbl: &mut Problem, runners: &'r SmtRunner) -> anyhow::Result<Self> {
        let mut cache = Self {
            files: Default::default(),
            runners,
            nasserts: NonZeroU32::new(1).unwrap(),
        };

        let SmtRunner { vampire, z3, cvc5 } = runners;

        if vampire.is_some() {
            cache.files.vampire = Some(CachedFile::new("vampire", pbl)?);
        }
        if z3.is_some() {
            cache.files.z3 = Some(CachedFile::new("z3", pbl)?);
        }
        if cvc5.is_some() {
            cache.files.cvc5 = Some(CachedFile::new("cvc5", pbl)?);
        }
        Ok(cache)
    }

    pub fn clear_files(&mut self, pbl: &mut Problem) -> anyhow::Result<()> {
        if let Some(CachedFile { file, .. }) = self.files.as_mut().vampire
        // && file.as_file().metadata()?.len() == 0
        {
            *file = mk_temp_file("vampire", pbl)?;
        }
        if let Some(CachedFile { file, .. }) = self.files.as_mut().z3
        // && file.as_file().metadata()?.len() == 0
        {
            *file = mk_temp_file("z3", pbl)?;
        }
        if let Some(CachedFile { file, .. }) = self.files.as_mut().cvc5
        // && file.as_file().metadata()?.len() == 0
        {
            *file = mk_temp_file("cvc5", pbl)?;
        }

        Ok(())
    }

    pub fn write_cache(&mut self) -> ::std::io::Result<()> {
        for c in self.files.as_mut() {
            c.write_cache()?
        }
        Ok(())
    }

    pub fn vampire_file(&self) -> Option<&Path> {
        self.files.vampire.as_ref().map(CachedFile::path)
    }

    pub fn z3_file(&self) -> Option<&Path> {
        self.files.z3.as_ref().map(CachedFile::path)
    }

    pub fn cvc5_file(&self) -> Option<&Path> {
        self.files.cvc5.as_ref().map(CachedFile::path)
    }
}

impl<'a, 'r> SmtSink<'a> for FileSink<'r> {
    fn extend_smt(&mut self, _pbl: &Problem, opts: &SmtOption, iter: utils::implvec!(MSmt<'a>)) {
        let Self {
            files,
            runners,
            nasserts,
        } = self;

        for command in iter {
            let comment = command.is_any_assert().then(|| {
                let n = *nasserts;
                *nasserts = nasserts.checked_add(1).unwrap();
                format!(";; {}\n", n)
            });

            let cmd = &command;
            let comment = comment.as_deref();

            mwrite(opts, cmd, comment, files, &runners.vampire).unwrap();
            mwrite(opts, cmd, comment, files, &runners.z3).unwrap();
            mwrite(opts, cmd, comment, files, &runners.cvc5).unwrap();
        }
    }

    fn reserve(&mut self, _: usize) {}
}

fn mwrite<'a, R: Runner>(
    options: &SmtOption,
    command: &MSmt<'a>,
    comment: Option<&str>,
    files: &mut RunnerSplitter<CachedFile>,
    runner: &Option<R>,
) -> anyhow::Result<()> {
    ereturn_let!(let Some(runner) = runner.as_ref(), Ok(()));
    let CachedFile { file, cache } = runner.mut_splitter(files).unwrap();
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
        use std::fmt::Write;
        writeln!(&mut str, "{cmd}")?;
    }

    if !options.depend_on_context {
        use std::fmt::Write;
        writeln!(cache, "{str}")?;
    }

    {
        use std::io::Write;
        write!(file, "{str}")?
    }
    Ok(())
}
