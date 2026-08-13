#![allow(dead_code)]
use std::fmt::Display;

use anyhow::{Context, anyhow, bail, ensure};
use bon::bon;
use clap::builder;
use itertools::Itertools;
use logic_formula::AsFormula;
use logic_formula::iterators::AllTermsIterator;
use thiserror::Error;
use utils::implvec;

use crate::terms::{EQ, FOBinder, Formula, Sort};

#[bon]
impl Formula {
    #[builder]
    pub fn type_check(&self, #[builder(default = true)] recurse: bool) -> anyhow::Result<()> {
        for t in self.iter_with(AllTermsIterator, ()) {
            match t {
                Self::Quantifier {
                    head: FOBinder::FindSuchThat,
                    arg,
                    ..
                } => {
                    check_sign(
                        self,
                        arg.iter(),
                        [Sort::Bool, Sort::Bitstring, Sort::Bitstring],
                        recurse,
                    )?;
                }
                Self::Quantifier { arg, .. } => {
                    check_sign(self, arg.iter(), [Sort::Bool], recurse)?
                }
                Self::App { head, args } if head == &EQ => {
                    if let (Some(sl), Some(sr)) = args
                        .iter()
                        .map(Formula::try_get_sort)
                        .collect_tuple()
                        .with_context(|| {
                            format!("wrong number of arguments in {self} (expecting 2)")
                        })?
                    {
                        ensure!(
                            sl.unify(sr),
                            "both side of the equality shhould have the same sort. Left is {sl} \
                             while right is {sr} in {self}"
                        )
                    }
                }
                Self::App { head, args } => {
                    check_sign(self, args.iter(), head.args_sorts(), recurse)?
                }
                Self::Var(_) => (),
            }
        }
        Ok(())
    }
}

fn check_sign<'a>(
    context: &'a Formula,
    args: implvec!(&'a Formula),
    expected_sorts: implvec!(Sort),
    recurse: bool,
) -> anyhow::Result<()> {
    for (i, e) in Itertools::zip_longest(args.into_iter(), expected_sorts).enumerate() {
        match e {
            itertools::EitherOrBoth::Both(f, s) => check_sign_one(context, f, s, recurse)?,
            itertools::EitherOrBoth::Left(_) => bail!(
                "too many arguments: got at least {:} but expected {i:} in {context}",
                i + 1
            ),
            itertools::EitherOrBoth::Right(_) => {
                bail!("too many few arguments in {context}")
            }
        }
    }
    Ok(())
}

fn check_sign_one(
    context: &Formula,
    arg: &Formula,
    expected_sort: Sort,
    recurse: bool,
) -> anyhow::Result<()> {
    if recurse {
        arg.type_check().recurse(recurse).call()?;
    }
    let s = arg.try_get_sort();
    if !s.unwrap_or(expected_sort).unify(expected_sort) {
        let s = s.unwrap(); // cannot fail otherwise we wouldn't be in this branch
        Err(anyhow!(
            "{arg} should have sort {expected_sort} but instead has {s}, in {context}"
        ))
    } else {
        Ok(())
    }
}
