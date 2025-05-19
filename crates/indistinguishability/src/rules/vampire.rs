use std::{borrow::Cow, io::Write};

use anyhow::Context;
use egg::{Analysis, Language, Pattern, Searcher, SymbolLang, Var};
use itertools::Itertools;
use runner::VampireExec;
use serde::Serialize;
use static_init::dynamic;
use utils::{ereturn_if, ereturn_let};

use golgge::Dependancy;

use golgge::Rule;

#[dynamic]
static PATTERN: Pattern<SymbolLang> = "(vampire ?x)".parse().unwrap();

#[dynamic]
static VAR: Var = "?x".parse().unwrap();

/// A rule that calls vampire to get its answer
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VampireRule {
    prelude: Cow<'static, str>,
    itimeout: u64,
}

impl VampireRule {
    pub fn new(prelude: Cow<'static, str>, itimeout: u64) -> Self {
        Self { prelude, itimeout }
    }
}

impl<N> Rule<SymbolLang, N> for VampireRule
where
    N: Default + Analysis<SymbolLang> + Serialize,
    N::Data: Serialize,
{
    fn search(
        &self,
        prgm: &mut golgge::Program<SymbolLang, N>,
        goal: egg::Id,
    ) -> golgge::Dependancy {
        ereturn_let!(let Some(m) = PATTERN.search_eclass(prgm.egraph(), goal), Default::default());
        ereturn_let!(let Some(s) = m.substs.first(), Default::default());

        let to_prove_id = s.get(*VAR).unwrap();
        let to_prove = prgm.egraph().id_to_expr(*to_prove_id);
        let mut to_prove = AsFun::try_from(to_prove.as_ref()).unwrap();
        to_prove.simplify();

        let mut tptp_file = tempfile::Builder::new()
            .prefix("vampire_rule_")
            .suffix(".smt")
            .keep(true)
            .tempfile()
            .unwrap();

        writeln!(&mut tptp_file, "{}", self.prelude).unwrap();
        write!(&mut tptp_file, "(assert-not ").unwrap();
        to_prove.to_smt(&mut tptp_file).unwrap();
        write!(&mut tptp_file, " )").unwrap();
        // to_tptp(&mut tptp_file, &to_prove).unwrap();

        eprintln!("running vampire from {:?}", tptp_file.path());

        let exec = VampireExec {
            exe_location: "vampire".into(),
            extra_args: {
                use runner::VampireArg::*;
                vec![
                    Cores(7),
                    Mode(runner::vampire_suboptions::Mode::Portfolio),
                    TimeLimit(1.0),
                ]
            },
        };

        let res = exec.run(tptp_file.path()).unwrap();

        if res {
            Dependancy::new(vec![vec![]])
        } else {
            Default::default()
        }
    }
}

struct AsFun<'a> {
    fun: Cow<'a, str>,
    args: Vec<AsFun<'a>>,
}

impl<'a> AsFun<'a> {
    pub fn to_smt(&self, f: &mut impl std::io::Write) -> anyhow::Result<()> {
        write!(f, "(")?;
        write!(f, "{}", self.fun)?;
        if !self.args.is_empty() {
            for arg in &self.args {
                arg.to_smt(f)?;
                write!(f, " ")?;
            }
        }
        write!(f, ")")?;
        Ok(())
    }

    pub fn simplify(&mut self) {
        let Self { fun, args } = self;

        args.iter_mut().for_each(Self::simplify);

        match fun.as_ref() {
            "macro" | "unfold" => {
                let kind = args.remove(0).fun;
                *fun = format!("{fun}_{kind}").into()
            }
            _ => (),
        }
    }

    pub fn used_funs(&self) -> Vec<&str> {
        let mut tmp = Vec::new();
        self.used_fun_innner(&mut tmp);
        tmp
    }

    fn used_fun_innner(&'a self, acc: &mut Vec<&'a str>) {
        acc.push(self.fun.as_ref());
        for arg in &self.args {
            arg.used_fun_innner(acc);
        }
    }
}

impl TryFrom<&[SymbolLang]> for AsFun<'_> {
    type Error = anyhow::Error;

    fn try_from(value: &[SymbolLang]) -> Result<Self, Self::Error> {
        let head = value.last().with_context(|| "impossible")?;
        let fun = head.op.as_str().into();
        let args: Vec<AsFun<'_>> = head
            .children()
            .iter()
            .map(|&i| usize::from(i))
            .map(|child| AsFun::try_from(&value[0..=child]))
            .try_collect()?;
        Ok(AsFun { fun, args })
    }
}

fn to_tptp(f: &mut impl std::io::Write, expr: &[SymbolLang]) -> anyhow::Result<()> {
    eprintln!("{:?}", expr);
    ereturn_let!(let Some(fun) = expr.last(), Err(anyhow::anyhow!("no expression to write !")));
    write!(f, "'{}'", fun.op.as_str())?;

    let children = fun.children();
    ereturn_if!(children.is_empty(), Ok(()));

    write!(f, "(")?;
    let mut children = children.iter();
    let mut mchild = children.next();
    while let Some(child) = mchild {
        let i = usize::from(*child);
        to_tptp(f, &expr[0..=i])?;
        mchild = children.next();
        if mchild.is_some() {
            write!(f, ", ")?;
        }
    }
    write!(f, ")")?;
    Ok(())
}

mod runner {
    use std::{
        path::{Path, PathBuf},
        process::Command,
    };

    /// The [Runner] itself
    #[derive(Debug, Clone)]
    pub struct VampireExec {
        pub exe_location: PathBuf,
        pub extra_args: Vec<VampireArg>,
    }

    macro_rules! option {
      ($($variant:ident($name:literal, $content:ty)),*,) => {
          #[allow(dead_code)]
          #[doc = "arguments to [VampireExec] in type-safeish mode"]
          #[derive(Debug, Clone, PartialEq, PartialOrd)]
          pub enum VampireArg {
            $($variant($content)),*
          }

          impl ToArgs<2> for VampireArg {
            fn to_args(&self) -> [String;2] {
              match self {
                $(Self::$variant(x) => {let [y] = x.to_args(); [format!("--{:}", $name).into(), y]})*
              }
            }
          }
      };
    }

    option!(
        Cores("cores", u64),
        MemoryLimit("memory_limit", u64),
        Mode("mode", vampire_suboptions::Mode),
        Slowness("slowness", u64),
        TimeLimit("time_limit", f64),
        InputSyntax("input_syntax", vampire_suboptions::InputSyntax),
        NewCnf("newcnf", bool),
        SaturationAlgorithm(
            "saturation_algorithm",
            vampire_suboptions::SaturationAlgorithm
        ),
        Avatar("avatar", bool),
        SatSolver("sat_solver", vampire_suboptions::SatSolver),
        ShowNew("show_new", bool),
        InlineLet("inline_let", bool),
    );

    pub mod vampire_suboptions {
        use super::ToArgs;
        macro_rules! suboption {
          ($name:ident, $(($variant:ident, $content:literal)),*,) => {
              #[allow(dead_code)]
              #[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd, Hash, Copy)]
              pub enum $name {
                $($variant),*
              }

              impl ToArgs<1> for $name {
                fn to_args(&self) -> [String;1] {
                  match self {
                    $(Self::$variant => [$content.into()]),*
                  }
                }
              }
          };
  }

        suboption!(Mode, (Portfolio, "portfolio"),);
        suboption!(
            InputSyntax,
            (SmtLib2, "smtlib2"),
            (Tptp, "tptp"),
            (Auto, "auto"),
        );
        suboption!(
            SaturationAlgorithm,
            (Discount, "discount"),
            (Otter, "otter"),
            (LimitedResources, "lrs"),
            (FiniteModel, "fmb"),
            (Z3, "z3"),
        );
        suboption!(SatSolver, (Minisat, "minisat"), (Z3, "z3"),);
    }

    /// Turn something into an array of [str] for the [Command] object
    trait ToArgs<const N: usize> {
        fn to_args(&self) -> [String; N];
    }

    impl ToArgs<1> for u64 {
        fn to_args(&self) -> [String; 1] {
            [self.to_string()]
        }
    }

    impl ToArgs<1> for f64 {
        fn to_args(&self) -> [String; 1] {
            [self.to_string()]
        }
    }

    impl ToArgs<1> for bool {
        fn to_args(&self) -> [String; 1] {
            [if *self { "on" } else { "off" }.into()]
        }
    }

    /// Success return code
    const SUCCESS_RC: i32 = 0;
    /// Timeout return code
    const TIMEOUT_RC: i32 = 1;

    impl VampireExec {
        pub fn run(&self, file: &Path) -> anyhow::Result<bool> {
            let mut cmd = Command::new(&self.exe_location);
            cmd.args(self.extra_args.iter().flat_map(|x| x.to_args().into_iter()));
            cmd.arg(file);
            let o = cmd.output()?;
            if o.status.code() != Some(SUCCESS_RC) && o.status.code() != Some(TIMEOUT_RC) {
                println!("{}", std::str::from_utf8(&o.stdout).unwrap());
                println!("{:}", o.status.code().unwrap());
                panic!()
            }

            println!(
                "{}",
                std::str::from_utf8(&o.stdout)
                    .unwrap()
                    .contains("Termination reason: Refutation\n")
            );

            Ok(o.status.success()
                && std::str::from_utf8(&o.stdout)
                    .unwrap()
                    .contains("Termination reason: Refutation\n"))
        }
    }
}
