use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitOr, Not, Shr};

use anyhow::{Context, bail};
use bon::Builder;
use cryptovampire_smt::{SmtFormula, SmtHead};
use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr};
use itertools::{Either, Itertools, chain, izip};
use log::{error, trace, warn};
use logic_formula::{Destructed, Formula, HeadSk};
use quarck::CowArc;
use rpds::HashTrieSet;
use rustc_hash::FxHashMap;
use serde::Serialize;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel::{SteelErr, rerrs};
use steel_derive::Steel;
use utils::{dynamic_iter, econtinue_let, ereturn_if, ereturn_let, implvec, match_eq};

use super::RecFOFormula;
use super::{FOBinder, RecFOFormulaQuant};
use crate::input::Registerable;
use crate::terms::formula::egg::EggLanguage;
use crate::terms::formula::sexpr::SExpr;
use crate::terms::formula::{RecFOFormulaQuantRef, list};
use crate::terms::utils::pull_from_egraph;
use crate::terms::{
    AND, BITE, CONS, EMPTY, EQ, FALSE, Function, IMPLIES, LAMBDA_O, LAMBDA_S, NIL, NOT, OR, Sort,
    TRUE, TUPLE, Variable,
};
use crate::{Lang, LangVar, MSmtFormula, fresh, rexp};

impl RecFOFormula {
    pub fn from_egg(formula: &[LangVar], sort: Option<Sort>) -> Self {
        let mut free_vars = Default::default();
        let mut db_free_vars = Default::default();
        Self::inner_from_egg(
            formula,
            Default::default(),
            0,
            &mut free_vars,
            &mut db_free_vars,
            sort,
        )
    }

    /// - formula: The formula to convert. It must be a valid reference to a [egg:RecExpr]
    /// - bound_variables: a queue use to track the De Bruijn indices and assign them names
    /// - free_variables: a map to transfrom [egg]'s free variables into cryptovampire's
    /// - possible_sort: the possible output sort of the formula
    fn inner_from_egg(
        formula: &[LangVar],
        bound_variables: rpds::Queue<Variable>,
        depth: usize,
        free_variables: &mut FxHashMap<egg::Var, Variable>,
        db_free_variables: &mut Vec<Variable>,
        possible_sort: Option<Sort>,
    ) -> Self {
        let head = formula.last().expect("we expect a non empty formula");

        use egg::ENodeOrVar::{ENode, Var};
        match head {
            Var(var) => {
                // get the variable from `free_variables` or spawn a fresh one (and save it)
                let var = free_variables
                    .entry(*var)
                    .or_insert(Variable::fresh().maybe_sort(possible_sort).call());
                Self::Var(var.clone())
            }
            ENode(Lang { head, args }) => {
                assert!(
                    possible_sort.is_none() || Some(head.signature.output) == possible_sort,
                    "the expected sort doesn't match the computed sort (expected {:?}, got {})",
                    possible_sort,
                    head.signature.output
                );
                let mut args = args.iter().map(|&i| &formula[..=usize::from(i)]);

                if head == &LAMBDA_O {
                    // `head` is a De Bruijn variable
                    assert!(
                        args.next().is_none(),
                        "De Bruijn variables shouldn't have parameters"
                    );
                    let var = match bound_variables.peek() {
                        Some(var) => var.clone(),
                        None => {
                            // this is a free De Bruijn variable
                            if db_free_variables.len() <= depth {
                                // extend the free de Bruijn variables if necessary
                                db_free_variables
                                    .extend((db_free_variables.len()..=depth).map(|_| fresh!()));
                            }
                            db_free_variables[depth].clone()
                        }
                    };
                    var.maybe_set_sort(possible_sort).unwrap();
                    Self::Var(var)
                } else if head == &LAMBDA_S {
                    // `head` is an S
                    let arg = {
                        let a1 = args.next();
                        let a2 = args.next();
                        match (a1, a2) {
                            (Some(x), None) => x,
                            _ => panic!("wrong number of argument for `S`"),
                        }
                    };

                    let (bound_variables, depth) = match bound_variables.dequeue() {
                        Some(x) => (x, depth), // if I can dequeue, the depth doesn't change
                        None => (bound_variables, depth + 1), // otherwise I increase the depth
                    };
                    Self::inner_from_egg(
                        arg,
                        bound_variables,
                        depth,
                        free_variables,
                        db_free_variables,
                        possible_sort,
                    )
                } else if let Some(binder) = head.as_fobinder() {
                    // an egg binder

                    // fetch the sort list
                    let sorts = {
                        let sort_exp = args.next().expect("a list of sorts as first arg");
                        list::try_get(Self::from(sort_exp)).expect("a list of sorts as first arg")
                    };
                    assert!(!sorts.is_empty(), "should be non-empty binder");

                    // we enque fresh variables
                    let mut bound_variables = bound_variables;
                    let mut vars = Vec::with_capacity(sorts.len());
                    for &sort in &sorts {
                        let variable = fresh!(sort);
                        vars.push(variable.clone());
                        bound_variables = bound_variables.enqueue(variable)
                    }

                    // compute the argument(s)
                    let args = Itertools::zip_eq(head.signature.inputs.iter(), args)
                        .map(|(&sort, arg)| {
                            Self::inner_from_egg(
                                arg,
                                bound_variables.clone(),
                                depth,
                                free_variables,
                                db_free_variables,
                                Some(sort),
                            )
                        })
                        .collect_vec();

                    // finish
                    assert!(
                        args.len() == binder.arity(),
                        "wrong number of argument for binder"
                    );
                    Self::Quantifier {
                        head: binder,
                        vars: vars.into(),
                        arg: args.into(),
                    }
                } else {
                    // a regular function
                    let args = Itertools::zip_eq(head.signature.inputs.iter(), args).map(
                        |(&sort, arg)| {
                            Self::inner_from_egg(
                                arg,
                                bound_variables.clone(),
                                depth,
                                free_variables,
                                db_free_variables,
                                Some(sort),
                            )
                        },
                    );
                    Self::App {
                        head: head.clone(),
                        args: Vec::from_iter(args).into(),
                    }
                }
            }
        }
    }

    /// shortcut for `self.as_egg::<LangVar>()`
    pub fn as_egg_var(&self) -> RecExpr<LangVar> {
        RecExpr::from(self.as_egg::<LangVar>())
    }

    /// shortcut for `self.as_egg::<Lang>()`
    pub fn as_egg_ground(&self) -> RecExpr<Lang> {
        RecExpr::from(self.as_egg::<Lang>())
    }

    /// Converts a `RecFOFormula` into a `egg`-like formula.
    ///
    /// `L` lets you decide the `egg::Language` to be used. It panics if the conversion is impossible.
    pub fn as_egg<L: EggLanguage>(&self) -> Vec<L> {
        let mut out = Vec::new();
        self.as_egg_inner(&mut out, Default::default(), Default::default(), &mut None);
        out
    }

    /// Converts a `RecFOFormula` into a `egg`-like formula.
    ///
    /// `L` lets you decide the `egg::Language` to be used. It panics if the conversion is impossible.
    pub fn as_egg_non_capture_avoiding<L: EggLanguage>(&self) -> Vec<L> {
        let mut out = Vec::new();
        self.as_egg_inner(
            &mut out,
            Default::default(),
            AsEggParam {
                capture_avoiding: false,
                ..Default::default()
            },
            &mut None,
        );
        out
    }

    fn as_egg_inner<'a, L: EggLanguage>(
        &'a self,
        out: &mut Vec<L>,
        mut bvars: rpds::HashTrieMap<&'a Variable, usize>,
        param: AsEggParam,
        olocation: &mut Option<usize>,
    ) -> usize {
        match self {
            Self::Quantifier { head, vars, arg } => {
                if !vars.is_empty() {
                    let l = match olocation {
                        Some(l) => *l,
                        None => {
                            let i = out.len();
                            *olocation = Some(i);
                            out.push(L::mk_fun_application(LAMBDA_O.clone(), []));
                            i
                        }
                    };

                    // update the variables assignement
                    bvars = bvars
                        .into_iter()
                        .map(|(v, i)| {
                            let mut i = *i;
                            for _ in vars.iter() {
                                out.push(L::mk_fun_application(LAMBDA_S.clone(), [Id::from(i)]));
                                i = out.len() - 1;
                            }
                            (*v, i)
                        })
                        .collect();

                    // mk the variables
                    {
                        let mut vars = vars.iter().rev();
                        let v1 = vars.next().unwrap();
                        bvars = bvars.insert(v1, l);
                        let mut l = l;
                        for v in vars {
                            out.push(L::mk_fun_application(LAMBDA_S.clone(), [Id::from(l)]));
                            l = out.len() - 1;
                            bvars = bvars.insert(v, l);
                        }
                    }
                }

                let mut nargs = Vec::with_capacity(arg.len() + 1);
                nargs.push(mk_list(out, vars.iter().map(|v| v.get_sort().unwrap())));
                nargs.extend(
                    arg.iter()
                        .map(|arg| arg.as_egg_inner(out, bvars.clone(), param.clone(), olocation)),
                );

                let head = head.as_function().cloned().unwrap();
                let nargs = nargs.into_iter().map(Id::from);
                out.push(L::mk_fun_application(head, nargs));
            }
            Self::App { head, args } => {
                let args = args
                    .iter()
                    .map(|arg| arg.as_egg_inner(out, bvars.clone(), param.clone(), olocation))
                    .map(Id::from)
                    .collect_vec();
                out.push(L::mk_fun_application(head.clone(), args));
            }
            Self::Var(variable) => match bvars.get(variable) {
                Some(i) => {
                    out.extend(mk_bound_var(*i));
                }
                None if (!param.capture_avoiding)
                    || param.non_capture_avoiding.contains(variable) =>
                {
                    out.push(L::mk_variable(variable))
                }
                None => {
                    let nparam = AsEggParam {
                        capture_avoiding: false,
                        ..param
                    };
                    bvars
                        .iter()
                        .fold(self.clone(), |acc, _| rexp!((LAMBDA_S #acc)))
                        .as_egg_inner(out, bvars, nparam, olocation);
                }
            },
        };

        out.len() - 1
    }

    // ~~~~~~~~~~~~~~ from graph ~~~~~~~~~~~~~~~~

    fn from_id_inner(ids: &[Id], langs: &[Option<&Lang>], current: &Lang) -> Self {
        let head = current.head.clone();
        let args = current
            .args
            .iter()
            .map(|id| ids.iter().position(|x| x == id).unwrap())
            .map(|i| langs[i].unwrap())
            .map(|l| Self::from_id_inner(ids, langs, l))
            .collect();
        Self::App { head, args }
    }

    /// remove any De-Buijn indices from a [Self]
    fn remove_de_bruijn(
        &self,
        bound_vars: &rpds::Queue<Variable>,
        depth: usize,
        free_vars: &mut Vec<Variable>,
    ) -> Option<Self> {
        match self {
            Self::Var(variable) => Some(Self::Var(variable.clone())),
            Self::Quantifier { head, vars, arg } => Some(Self::Quantifier {
                head: *head,
                vars: vars.clone(),
                arg: arg
                    .iter()
                    .map(|x| x.remove_de_bruijn(bound_vars, depth, free_vars))
                    .collect::<Option<cowarc![_]>>()?,
            }),
            Self::App { head, args } => {
                if head == &LAMBDA_O {
                    let var = bound_vars
                        .peek()
                        .cloned()
                        .unwrap_or_else(|| free_vars[depth].clone());
                    Some(Self::Var(var))
                } else if head == &LAMBDA_S {
                    match bound_vars.dequeue() {
                        Some(bound_vars) => {
                            args.first()?
                                .remove_de_bruijn(&bound_vars, depth, free_vars)
                        }
                        None => {
                            free_vars.push(fresh!());
                            args.first()?
                                .remove_de_bruijn(bound_vars, depth + 1, free_vars)
                        }
                    }
                } else if let Some(bind) = head.as_fobinder() {
                    let mut args = args.iter();

                    let sorts = Sort::list_from_formula(args.next()?)?;
                    let variables: cowarc![_] = sorts.into_iter().map(|s| fresh!(s)).collect();

                    let bound_vars = variables
                        .iter()
                        .fold(bound_vars.clone(), |acc, v| acc.enqueue(v.clone()));

                    let args = args
                        .map(|arg| arg.remove_de_bruijn(&bound_vars, depth, free_vars))
                        .collect::<Option<cowarc![_]>>()?;
                    ereturn_if!(args.len() != bind.arity(), None);

                    Some(Self::Quantifier {
                        head: bind,
                        vars: variables,
                        arg: args,
                    })
                } else {
                    let args = args
                        .iter()
                        .map(|x| x.remove_de_bruijn(bound_vars, depth, free_vars))
                        .collect::<Option<cowarc![_]>>()?;
                    Some(Self::App {
                        head: head.clone(),
                        args,
                    })
                }
            }
        }
    }

    /// extract a [Self] from an [EGraph]. This is a raw translation from
    /// [golgge], notably `egg`-style quantifiers are still there
    fn pull_from_egraph<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> Result<Self, Id> {
        let mut id_buffer = Vec::new();
        let mut recexpr_buffer = Vec::new();

        pull_from_egraph::inner(egraph, id, &mut id_buffer, &mut recexpr_buffer)?;

        // all the ids referenced in `recexpr_buffer` are in `id_buffer`
        debug_assert!(
            recexpr_buffer
                .iter()
                .flat_map(|x| x.as_ref().into_iter())
                .flat_map(|l| l.children())
                .all(|c| id_buffer.contains(c))
        );

        Ok(Self::from_id_inner(
            &id_buffer,
            &recexpr_buffer,
            recexpr_buffer.first().unwrap().unwrap(),
        ))
    }

    pub fn try_from_id<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
    ) -> anyhow::Result<Self> {
        Self::try_from_id_with_vars(egraph, id, &Default::default())
    }

    pub fn try_from_id_with_vars<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
        vars: &rpds::Queue<Variable>,
    ) -> anyhow::Result<Self> {
        let var = match Self::pull_from_egraph(egraph, id) {
            Ok(f) => f,
            Err(id) => {
                let s = egraph.id_to_expr(id).pretty(100);
                bail!("{id} is a formula that is not translatable to smt:\n\t{s}");
            }
        };

        var.remove_de_bruijn(vars, 0, &mut vec![fresh!()])
            .with_context(|| format!("couldn't remove de bruijin indices in {var}"))
    }

    // ~~~~~~~~~~~~~~~~~ smt ~~~~~~~~~~~~~~~~~~~~

    // #[deprecated]
    // pub fn try_from_subts<N: Analysis<Lang>>(
    //     egraph: &EGraph<Lang, N>,
    //     subst: &egg::Subst,
    //     var: &Variable,
    // ) -> Option<Self> {
    //     Self::try_from_id(egraph, *subst.get(var.as_egg())?)
    // }
}

#[derive(Debug, Clone)]
pub struct AsEggParam {
    pub capture_avoiding: bool,
    pub non_capture_avoiding: ::rpds::HashTrieSet<Variable>,
}

impl Default for AsEggParam {
    fn default() -> Self {
        Self {
            non_capture_avoiding: Default::default(),
            capture_avoiding: true,
        }
    }
}

fn mk_list<L: EggLanguage>(out: &mut Vec<L>, sorts: implvec!(Sort)) -> usize {
    let sorts = sorts.into_iter();
    let mut i = out.len();
    out.reserve(sorts.size_hint().0 * 2 + 1);
    out.push(L::mk_fun_application(NIL.clone(), []));

    for sort in sorts {
        let sort = sort.as_function().unwrap();
        out.push(EggLanguage::mk_fun_application(sort.clone(), []));
        out.push(EggLanguage::mk_fun_application(
            CONS.clone(),
            [i + 1, i].map(Id::from),
        ));
        i += 2
    }
    i
}

fn mk_bound_var<L: EggLanguage>(depth: usize) -> impl Iterator<Item = L> {
    chain![
        ::std::iter::once(L::mk_fun_application(LAMBDA_O.clone(), [])),
        (0..depth).map(|i| L::mk_fun_application(LAMBDA_S.clone(), [Id::from(i)]))
    ]
}

impl From<&[LangVar]> for RecFOFormula {
    fn from(v: &[LangVar]) -> Self {
        Self::from_egg(v, None)
    }
}

impl From<&RecExpr<LangVar>> for RecFOFormula {
    fn from(value: &RecExpr<LangVar>) -> Self {
        Self::from_egg(value.as_ref(), None)
    }
}

impl From<RecExpr<LangVar>> for RecFOFormula {
    fn from(value: RecExpr<LangVar>) -> Self {
        Self::from(&value)
    }
}

impl From<bool> for RecFOFormula {
    fn from(value: bool) -> Self {
        match value {
            true => Self::True(),
            false => Self::False(),
        }
    }
}

impl From<Variable> for RecFOFormula {
    fn from(value: Variable) -> Self {
        Self::Var(value)
    }
}

impl From<&Variable> for RecFOFormula {
    fn from(value: &Variable) -> Self {
        Self::Var(value.clone())
    }
}

impl From<&RecFOFormula> for RecExpr<LangVar> {
    fn from(value: &RecFOFormula) -> Self {
        value.as_egg().into()
    }
}

impl From<&RecFOFormula> for Pattern<Lang> {
    fn from(value: &RecFOFormula) -> Self {
        Pattern::from(RecExpr::from(value))
    }
}


#[cfg(test)]
mod conversion_tests {
    use egg::PatternAst;

    use crate::{Lang, decl_vars, rexp};

    #[test]
    fn as_egg_succ() {
        decl_vars!(a, b);
        let f = rexp!((and #a #b
                (exists ((#i Bitstring) (#j Bitstring))
                    (and #a #b (= #i #j)
                            (exists ((#i Bitstring) (#k Bitstring))
                                (and (= #i #k #j) #a))))));
        let f: PatternAst<Lang> = f.as_egg().into();
        println!("{}", f.pretty(100));
    }
}