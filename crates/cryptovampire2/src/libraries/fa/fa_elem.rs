use std::fmt::{Debug, Display};

use egg::{Analysis, EGraph, Id};
use itertools::Itertools;
use utils::dynamic_iter;

use super::split;
use crate::Lang;
use crate::libraries::utils::Side;
use crate::terms::{CONS_FA_BITSTRING, CONS_FA_BOOL, Function, Sort};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FaElem {
    pub a: Id,
    pub b: Id,
    pub sort: LSort,
    /// Can/should we keep on splitting ?
    ///
    /// NB: this field is useless later on
    pub splittable: bool,
}

/// Printable [FaElem]
struct PrintFa<'a, N: Analysis<Lang>> {
    egraph: &'a EGraph<Lang, N>,
    fa: &'a FaElem,
}

impl FaElem {
    pub fn get(&self, side: Side) -> Id {
        match side {
            Side::Left => self.a,
            Side::Right => self.b,
        }
    }

    pub fn set(&self, side: Side, x: Id) -> Self {
        match side {
            Side::Left => Self { a: x, ..*self },
            Side::Right => Self { b: x, ..*self },
        }
    }

    pub fn display<'a, N: Analysis<Lang>>(
        &'a self,
        egraph: &'a EGraph<Lang, N>,
    ) -> impl Display + use<'a, N> {
        PrintFa { egraph, fa: self }
    }

    /// In debug builds, panics if mistyping
    pub fn checks_sort<'a, N: Analysis<Lang>>(&'a self, egraph: &'a EGraph<Lang, N>) {
        for id in [self.a, self.b] {
            debug_assert!(
                egraph[id]
                    .nodes
                    .iter()
                    .map(|l| l.head.signature.output)
                    .filter(|s| s != &Sort::Any)
                    .chain(::std::iter::once(self.sort.as_sort()))
                    .all_equal(),
                "mistyping [{}]",
                egraph[id].nodes.iter().join(", ")
            );
        }
    }
}

impl<'a, N: Analysis<Lang>> Display for PrintFa<'a, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "FaElem {{\n\ta:'{}'\n\tb:'{}'\n,.. }}",
            self.egraph.id_to_expr(self.fa.a).pretty(100),
            self.egraph.id_to_expr(self.fa.b).pretty(100)
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LSort {
    Bool,
    Bitstring,
}

impl TryFrom<Sort> for LSort {
    type Error = ();

    fn try_from(value: Sort) -> Result<Self, Self::Error> {
        match value {
            Sort::Bool => Ok(LSort::Bool),
            Sort::Bitstring => Ok(LSort::Bitstring),
            _ => Err(()),
        }
    }
}

impl LSort {
    pub fn to_cons_fn(self) -> &'static Function {
        match self {
            Self::Bitstring => &CONS_FA_BITSTRING,
            Self::Bool => &CONS_FA_BOOL,
        }
    }

    pub fn as_sort(&self) -> Sort {
        match self {
            Self::Bitstring => Sort::Bitstring,
            Self::Bool => Sort::Bool,
        }
    }
}

pub fn split_all<N: Analysis<Lang>>(
    ida: Id,
    idb: Id,
    egraph: &EGraph<Lang, N>,
) -> Vec<Vec<FaElem>> {
    FaList::new(ida, idb).step_all(egraph)
}

/// Struct to split a [FaElem] into a list
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FaList {
    /// list of [FaElem] that still need to be dealt with
    todo: Vec<FaElem>,
    /// Those that are done
    done: Vec<FaElem>,
}

impl FaList {
    pub fn new(ida: Id, idb: Id) -> Self {
        Self {
            todo: vec![FaElem {
                a: ida,
                b: idb,
                sort: LSort::Bitstring,
                splittable: true,
            }],
            done: Default::default(),
        }
    }

    /// Is there anything left to do.
    pub fn is_done(&self) -> bool {
        self.todo.is_empty()
    }

    /// splits `self` once
    ///
    /// This is a wrapper around [split]. It returns an iterator of [Self]s
    /// ready to be used again
    ///
    /// **Panics** if [Self::is_done] returns false.
    pub fn step_one<N: Analysis<Lang>>(
        self,
        egraph: &EGraph<Lang, N>,
    ) -> impl Iterator<Item = Self> {
        dynamic_iter!(Iter; A:A, B:B);
        let FaList { mut todo, done } = self;

        match todo.pop() {
            Some(fa) => {
                let splitted = split(egraph, fa);
                if splitted.is_empty() {
                    Iter::A(::std::iter::once(FaList { todo, done }))
                } else {
                    Iter::B(splitted.into_iter().map(move |x| {
                        // x.into_iter().pa(|x| x.splittable);
                        let mut done = done.clone();
                        let mut todo = todo.clone();
                        for fa in x {
                            if fa.splittable {
                                tr!("ntodo {}", fa.display(egraph));
                                todo.push(fa);
                            } else {
                                tr!("done {}", fa.display(egraph));
                                done.push(fa);
                            }
                        }
                        tr!(
                            "todo = [{}]",
                            todo.iter().map(|x| x.display(egraph)).join(",\n")
                        );
                        FaList { todo, done }
                    }))
                }
            }
            _ => panic!("nothing to be done"),
        }
    }

    /// Spam [Self::step_one] until there is nothing else to do
    pub fn step_all<N: Analysis<Lang>>(self, egraph: &EGraph<Lang, N>) -> Vec<Vec<FaElem>> {
        let mut todo = vec![self];
        let mut done = Vec::new();

        while let Some(e) = todo.pop() {
            tr!(
                "todo.todo = [{}]",
                e.todo.iter().map(|x| x.display(egraph)).join(",\n")
            );
            if e.is_done() {
                done.push(e.done)
            } else {
                todo.extend(e.step_one(egraph));
            }
            tr!("{:}", todo.len());
        }
        done
    }
}
