pub mod builder;
mod declare_and_base;
mod preprocessing;

use std::collections::HashSet;

use bitflags::bitflags;
use itertools::Itertools;

use crate::{
    formula::{
        builtins::{functions::SUBTERM, types::BOOL},
        env::Environement,
        formula::{RichFormula, Variable},
        formula_iterator::{FormulaIterator, IteratorFlags},
        function::{FFlags, Function},
        sort::Sort,
    },
    problem::{problem::Problem, step::Step},
    smt::{
        macros::{sfun, simplies, sneq},
        smt::{Smt, SmtFormula},
    },
    utils::utils::StackBox,
};

use self::builder::Builder;

use super::Ctx;

bitflags! {
    #[derive(Default )]
    pub struct SubtermFlags: u8 {
        /// When used for side conditions, this lets you do away with all the `subterm input` & co
        const ALWAYS_PROCESSWIDE =      1 << 0;

    }
}

#[derive(Debug)]
pub struct Subterm<B> {
    sort: Sort,
    name: String,
    flags: SubtermFlags,
    ignored_functions: Vec<Function>,
    inner: InnerSubterm,
    builder: B,
}

#[derive(Debug)]
enum InnerSubterm {
    Vampire {
        high_order_fun: Function,
        function: Function,
    },
    SmtCompliant {
        sorts_order: Vec<Sort>,
        functions: Vec<Function>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SubtermKind {
    Vampire,
    SmtCompliant,
}

impl InnerSubterm {
    fn kind(&self) -> SubtermKind {
        match self {
            InnerSubterm::Vampire { .. } => SubtermKind::Vampire,
            InnerSubterm::SmtCompliant { .. } => SubtermKind::SmtCompliant,
        }
    }
}

impl From<&Environement> for SubtermKind {
    fn from(env: &Environement) -> Self {
        if env.use_special_subterm() {
            Self::Vampire
        } else {
            Self::SmtCompliant
        }
    }
}

impl<B> Subterm<B> {
    pub fn f(&self, a: SmtFormula, b: SmtFormula, sort: &Sort) -> SmtFormula {
        match &self.inner {
            InnerSubterm::Vampire {
                high_order_fun: sbt,
                function: f,
                ..
            } => sfun!(sbt; sfun!(f), a, b),
            InnerSubterm::SmtCompliant {
                sorts_order,
                functions: f,
                ..
            } => {
                let i = sorts_order
                    .iter()
                    .position(|s| s == sort)
                    .unwrap_or_else(|| panic!("{:?}", sort));
                sfun!(f[i]; a, b)
            }
        }
    }

    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn builder(&self) -> &B {
        &self.builder
    }

    fn new(
        ctx: &mut Ctx,
        kind: SubtermKind,
        sort: Sort,
        name: String,
        flags: SubtermFlags,
        ignored_functions: impl Iterator<Item = Function>,
        builder: B,
    ) -> Self {
        let bool = BOOL(ctx.env()).clone();
        let inner = match kind {
            SubtermKind::Vampire => {
                let f = Function::new_with_flag(&name, vec![], bool, FFlags::SUBTERM_FUN);
                assert!(ctx.env_mut().add_f(f.clone()));
                InnerSubterm::Vampire {
                    high_order_fun: SUBTERM(ctx.env()).clone(),
                    function: f,
                }
            }
            SubtermKind::SmtCompliant => {
                let sorts = ctx.env().get_sort_iter().cloned().collect_vec();
                let functions = sorts
                    .iter()
                    .map(|s| {
                        let f = Function::new_with_flag(
                            &format!("s$subterm_{}_{}", name, s.name()),
                            vec![sort.clone(), s.clone()],
                            bool,
                            FFlags::empty(),
                        );
                        assert!(ctx.env_mut().add_f(f.clone()));
                        f
                    })
                    .collect();
                InnerSubterm::SmtCompliant {
                    sorts_order: sorts,
                    functions,
                }
            }
        };

        Subterm {
            sort,
            name,
            flags,
            inner,
            ignored_functions: ignored_functions.collect_vec(),
            builder,
        }
    }

    pub fn kind(&self) -> SubtermKind {
        self.inner.kind()
    }

    pub fn commuting_functions<'a>(
        &'a self,
        env: &'a Environement,
    ) -> impl Iterator<Item = &'a Function> + 'a {
        let b = self.flags.contains(SubtermFlags::ALWAYS_PROCESSWIDE);
        env.get_functions_iter().filter(move |&f| {
            f.is_term_algebra()
                && (b || !f.is_special_subterm())
                && !self.ignored_functions.contains(&f)
                && !f.is_from_step()
        })
    }
}

impl<'a, B> Subterm<B>
where
    B: Builder<'a>,
{
    pub fn new_and_init(
        assertions: &mut Vec<Smt>,
        declarations: &mut Vec<Smt>,
        ctx: &mut Ctx,
        name: String,
        sort: Sort,
        ignored_functions: impl Iterator<Item = Function>,
        flags: SubtermFlags,
        builder: B,
    ) -> Self {
        let subt = Self::new(
            ctx,
            ctx.env().into(),
            sort,
            name,
            flags,
            ignored_functions,
            builder,
        );
        declare_and_base::declare_and_base(assertions, declarations, ctx, &subt);

        subt
    }
    pub fn builder_function(
        &self,
        m: &RichFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<RichFormula>, Vec<&'a RichFormula>) {
        self.builder().preprocess(self, m, s, pbl, f)
    }
}
