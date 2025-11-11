use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitOr, Not, Shr};

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

use super::{FOBinder, RecFOFormulaQuant};
use crate::input::Registerable;
use crate::terms::formula::egg::EggLanguage;
use crate::terms::formula::sexpr::SExpr;
use crate::terms::formula::unification::{self, Substitution};
use crate::terms::formula::{RecFOFormulaQuantRef, list};
use crate::terms::utils::pull_from_egraph;
use crate::terms::{
    AND, BITE, CONS, EMPTY, EQ, FALSE, Function, IMPLIES, LAMBDA_O, LAMBDA_S, NIL, NOT, OR, Sort,
    TRUE, TUPLE, Variable,
};
use crate::{Lang, LangVar, MSmtFormula, fresh, rexp};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Steel, Serialize)]
#[steel(equality, hash)]
pub enum RecFOFormula {
    Quantifier {
        head: FOBinder,
        vars: cowarc![Variable],
        arg: cowarc![Self],
    },
    App {
        head: Function,
        args: cowarc![Self],
    },
    Var(Variable),
}
impl RecFOFormula {
    pub fn as_var(&self) -> Option<&Variable> {
        match self {
            Self::Var(v) => Some(v),
            _ => None,
        }
    }

    /// Tries to evaluate an expression, return [None] if it can't
    pub fn try_evaluate(&self) -> Option<bool> {
        match self {
            RecFOFormula::App { head, args } => {
                match_eq! { head => {
                    TRUE => {Some(true)},
                    FALSE => {Some(false)},
                    NOT => {Some(!args[0].try_evaluate()?)},
                    AND => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(false) || r == Some(false) {
                            Some(false)
                        } else {
                            Some(l? && r?)
                        }
                    },
                    OR => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(true) || r == Some(true) {
                            Some(true)
                        } else {
                            Some(l? || r?)
                        }
                    },
                    IMPLIES => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(false) || r == Some(true) {
                            Some(true)
                        } else {
                            Some((!l?) || r?)
                        }
                    },
                    _ => {None}
                }}
            }
            RecFOFormula::Quantifier {
                head: FOBinder::Exists,
                arg,
                ..
            }
            | RecFOFormula::Quantifier {
                head: FOBinder::Forall,
                arg,
                ..
            } => arg[0].try_evaluate(),
            _ => None,
        }
    }

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
    fn pull_from_egraph<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> Option<Self> {
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

        Some(Self::from_id_inner(
            &id_buffer,
            &recexpr_buffer,
            recexpr_buffer.first().unwrap().unwrap(),
        ))
    }

    pub fn try_from_id<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> Option<Self> {
        Self::try_from_id_with_vars(egraph, id, &Default::default())
    }

    pub fn try_from_id_with_vars<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        id: Id,
        vars: &rpds::Queue<Variable>,
    ) -> Option<Self> {
        Self::pull_from_egraph(egraph, id)?.remove_de_bruijn(vars, 0, &mut vec![fresh!()])
    }

    /// Returns the [Sort] of `self`, [None] if it is a variable
    ///
    /// **NB**:
    /// - doesn't typechecks
    pub fn try_get_sort(&self) -> Option<Sort> {
        match self {
            RecFOFormula::Quantifier { .. } => Some(Sort::Bool),
            RecFOFormula::App { head, .. } => Some(head.signature.output),
            RecFOFormula::Var(_) => None,
        }
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Self::App { head, .. } if head == &TRUE)
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::App { head, .. } if head == &FALSE)
    }
}

// =========================================================
// ======================= is_xxx ==========================
// =========================================================
#[allow(dead_code)]
impl RecFOFormula {
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }
    #[must_use]
    pub fn is_app(&self) -> bool {
        matches!(self, Self::App { .. })
    }
    #[must_use]
    pub fn is_quantifier(&self) -> bool {
        matches!(self, Self::Quantifier { .. })
    }
}

// =========================================================
// ==================== manipulation =======================
// =========================================================
// substitution, unification, etc...

pub mod substitution_utils {
    use rustc_hash::FxHashMap;

    use crate::terms::Variable;

    #[non_exhaustive]
    #[derive(Debug)]
    pub struct AlphaArgs<'var, 'r> {
        pub var: &'var Variable,
        pub subst: &'r mut FxHashMap<&'var Variable, Variable>,
    }
}
use substitution_utils::*;

impl RecFOFormula {
    // ~~~~~~~~~~~~ alpha renaming ~~~~~~~~~~~~~~

    /// Renames the variables in `self` that verify `do_change` with fresh ones.
    /// It populate `subst` as it goes with the substitution it creates. If a
    /// substution was alreay there, it extends it.
    ///
    /// ## Notes
    /// - `do_change` has priority over the pre-existing substitution to
    ///   decide how to modify the variables
    /// - it effectively clones `self`.
    pub fn alpha_rename_if_with<'a>(
        &'a self,
        subst: &mut FxHashMap<&'a Variable, Variable>,
        do_change: &mut impl FnMut(AlphaArgs<'a, '_>) -> bool,
    ) -> Self {
        match self {
            Self::App { head, args } => Self::App {
                head: head.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.alpha_rename_if_with(subst, do_change))
                    .collect(),
            },
            Self::Var(var) => {
                if do_change(AlphaArgs { var, subst }) {
                    Self::Var(
                        subst
                            .entry(var)
                            .or_insert_with(|| Variable::fresh().maybe_sort(var.get_sort()).call())
                            .clone(),
                    )
                } else {
                    self.clone()
                }
            }
            Self::Quantifier { head, vars, arg } => {
                let head = *head;
                let vars = vars
                    .iter()
                    .map(|var| {
                        if do_change(AlphaArgs { var, subst }) {
                            subst
                                .entry(var)
                                .or_insert_with(|| {
                                    Variable::fresh().maybe_sort(var.get_sort()).call()
                                })
                                .clone()
                        } else {
                            var.clone()
                        }
                    })
                    .collect();
                let arg = arg
                    .iter()
                    .map(|arg| arg.alpha_rename_if_with(subst, do_change))
                    .collect();
                Self::Quantifier { head, vars, arg }
            }
        }
    }

    /// Freshen all the variables to ensure their uniqueness
    ///
    /// ## arguments
    /// - `predicate`: a function that return `true` if the variable must be
    ///   renamed
    pub fn alpha_rename_if(&self, mut do_change: impl FnMut(&Variable) -> bool) -> Self {
        self.alpha_rename_if_with(
            &mut FxHashMap::default(),
            &mut |AlphaArgs { var, .. }| do_change(var),
        )
    }

    /// Make all the variables apearing in `self` unique to `self`
    pub fn alpha_rename(&self) -> Self {
        self.alpha_rename_if_with(&mut FxHashMap::default(), &mut |_| true)
    }

    /// Apply a specific variable substitution
    pub fn apply_substitution<'a>(&'a self, subst: &mut FxHashMap<&'a Variable, Variable>) -> Self {
        self.alpha_rename_if_with(subst, &mut |AlphaArgs { var, subst }| {
            subst.contains_key(var)
        })
    }

    // ~~~~~~~~~~~~~ unification ~~~~~~~~~~~~~~~~
    pub fn unify(&self, other: &Self) -> Option<FxHashMap<Variable, Self>> {
        match unification::mgu(self, other) {
            Ok(Substitution(map)) => Some(map),
            Err(_) => None,
        }
    }

    /// capture avoiding substitution
    pub fn subst(&self, subst: &[(Variable, Self)]) -> Self {
        self.inner_subst(subst, &Default::default())
    }

    /// helper function for [Self::subst]
    fn inner_subst(&self, subst: &[(Variable, Self)], bvars: &HashTrieSet<Variable>) -> Self {
        match self {
            Self::Quantifier { head, vars, arg } => {
                let mut bvars = bvars.clone();
                for v in vars.iter() {
                    bvars.insert_mut(v.clone());
                }
                Self::Quantifier {
                    head: *head,
                    vars: vars.clone(),
                    arg: arg
                        .iter()
                        .map(|arg| arg.inner_subst(subst, &bvars))
                        .collect(),
                }
            }
            Self::App { head, args } => Self::App {
                head: head.clone(),
                args: args.iter().map(|x| x.inner_subst(subst, bvars)).collect(),
            },
            Self::Var(var) => if !bvars.contains(var)
                && let Some((_, expr)) = subst.iter().find(|(v, _)| v == var)
            {
                expr
            } else {
                self
            }
            .clone(),
        }
    }

    // new attemp

    /// Recursively applies a substitution to a formula.
    pub fn apply(&self, subst: &Substitution) -> Self {
        match self {
            // If we are a variable, check if we are in the substitution
            RecFOFormula::Var(v) => subst.0.get(v).cloned().unwrap_or_else(|| self.clone()),

            // For an application, apply to all arguments
            RecFOFormula::App { head, args } => RecFOFormula::App {
                head: head.clone(),
                args: args.iter().map(|arg| arg.apply(subst)).collect(),
            },

            // For a quantifier, we must apply the substitution *without*
            // touching variables that are shadowed by the quantifier's binders.
            RecFOFormula::Quantifier { head, vars, arg } => {
                // 1. Clone the substitution
                let mut shadowed_subst = subst.clone();

                // 2. Remove any bindings for variables that are now bound
                for v in vars.iter() {
                    shadowed_subst.0.remove(v);
                }

                // 3. Apply the filtered substitution to the body
                RecFOFormula::Quantifier {
                    head: head.clone(),
                    vars: vars.clone(),
                    arg: arg.iter().map(|x| x.apply(&shadowed_subst)).collect(),
                }
            }
        }
    }

    /// Checks if a variable occurs *free* within a formula.
    /// This is the "occurs check".
    pub fn contains_var(&self, var: &Variable) -> bool {
        match self {
            RecFOFormula::Var(v) => v == var,
            RecFOFormula::App { args, .. } => args.iter().any(|arg| arg.contains_var(var)),
            RecFOFormula::Quantifier { vars, arg, .. } => {
                // If the variable is bound by *this* quantifier, it does
                // not count as a free occurrence.
                if vars.iter().any(|v| v == var) {
                    false
                } else {
                    // Otherwise, check the body.
                    arg.iter().any(|arg| arg.contains_var(var))
                }
            }
        }
    }
}

fn find<'a>(
    var: &'a Variable,
    subst: &'a FxHashMap<Variable, RecFOFormula>,
    seen: &mut Vec<Variable>,
) -> Result<Either<&'a RecFOFormula, &'a Variable>, &'a Variable> {
    match subst.get(var) {
        Some(RecFOFormula::Var(nv)) if seen.contains(nv) => Err(var),
        Some(RecFOFormula::Var(var)) => {
            seen.push(var.clone());
            find(var, subst, seen)
        }
        Some(x) => Ok(Either::Left(x)),
        _ => Ok(Either::Right(var)),
    }
}

// =========================================================
// ===================== conversion ========================
// =========================================================
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
                            bvars = bvars.insert(&v, l);
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
                    || param.non_capture_avoiding.contains(&variable) =>
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

    pub fn as_pre_smt<'a, U>(&'a self) -> PreSmtRecFOFormulaF<'a, U> {
        PreSmtRecFOFormula::builder().formula(Cow::Borrowed(self))
    }

    pub fn into_pre_smt<'a, U>(self) -> PreSmtRecFOFormulaF<'a, U> {
        PreSmtRecFOFormula::builder().formula(Cow::Owned(self))
    }

    pub fn as_smt<U: QuantifierTranslator>(&self, pbl: &U) -> Option<MSmtFormula> {
        trace!("trying to translate to smt:\n{self}");
        match MSmtFormula::try_from(self.as_pre_smt().translator(pbl).build()) {
            Err(f) => {
                warn!("failed to turn into smt {f}");
                None
            }
            Ok(f) => {
                trace!("translated;\n\t{self}\nto:\n\t{f}");
                Some(f)
            }
        }
    }

    pub fn try_from_subts<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        subst: &egg::Subst,
        var: &Variable,
    ) -> Option<Self> {
        Self::try_from_id(egraph, *subst.get(var.as_egg())?)
    }
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

// =========================================================
// ================== specific builders ====================
// =========================================================
impl RecFOFormula {
    pub fn bind(kind: FOBinder, vars: Vec<Variable>, args: implvec!(RecFOFormula)) -> Self {
        assert!(vars.iter().all(Variable::has_sort));
        Self::Quantifier {
            head: kind,
            vars: vars.into(),
            arg: args.into_iter().collect(),
        }
    }

    pub fn app(fun: Function, args: Vec<Self>) -> Self {
        Self::App {
            head: fun,
            args: args.into(),
        }
    }

    pub fn fold(
        fun: &Function,
        args: implvec!(Self),
        default: Option<Self>,
        give_up_on_one: bool,
    ) -> Self {
        let mut args = args.into_iter();
        let a = args.next().unwrap_or_else(|| default.unwrap());
        let Some(b) = args.next() else {
            if give_up_on_one {
                panic!("giving up as requested")
            } else {
                return a;
            }
        };

        args.fold(Self::app(fun.clone(), vec![a, b]), |acc, x| {
            Self::app(fun.clone(), vec![acc, x])
        })
    }

    #[allow(non_snake_case)]
    pub const fn True() -> Self {
        Self::constant(TRUE.const_clone())
    }

    #[allow(non_snake_case)]
    pub const fn False() -> Self {
        Self::constant(FALSE.const_clone())
    }

    pub fn and(args: implvec!(Self)) -> Self {
        let mut args = args.into_iter().filter(|x| !x.is_true()).unique();
        ereturn_let!(let Some(init) = args.next(), Self::True());
        ereturn_if!(init.is_false(), Self::False());

        let mut ret = init;
        for c in args {
            ereturn_if!(c.is_false(), Self::False());
            ret = rexp!((AND #c #ret));
        }
        ret
    }

    pub fn or(args: implvec!(Self)) -> Self {
        let mut args = args.into_iter().filter(|x| !x.is_false()).unique();
        ereturn_let!(let Some(init) = args.next(), Self::False());
        ereturn_if!(init.is_true(), Self::True());

        let mut ret = init;
        for c in args {
            ereturn_if!(c.is_true(), Self::True());
            ret = rexp!((OR #c #ret));
        }
        ret
    }

    #[deprecated]
    pub fn optimised_binder(
        _kind: FOBinder,
        _vars: implvec!(Variable),
        _arg: RecFOFormula,
    ) -> Self {
        todo!()
    }

    /// Makes a constant
    pub const fn constant(head: Function) -> Self {
        Self::App {
            head,
            args: mk_cowarc![],
        }
    }

    pub const fn mk_const_app(head: Function, args: &'static [Self]) -> Self {
        Self::App {
            head,
            args: CowArc::Borrowed(args),
        }
    }

    pub const fn mk_var(var: Variable) -> Self {
        Self::Var(var)
    }

    pub const fn mk_const_quant(
        head: FOBinder,
        vars: &'static [Variable],
        arg: &'static [Self],
    ) -> Self {
        Self::Quantifier {
            head,
            vars: CowArc::Borrowed(vars),
            arg: CowArc::Borrowed(arg),
        }
    }

    pub const fn const_clone(&self) -> Self {
        match self {
            Self::Quantifier {
                head,
                vars: CowArc::Borrowed(vars),
                arg: CowArc::Borrowed(arg),
            } => Self::Quantifier {
                head: *head,
                vars: CowArc::Borrowed(*vars),
                arg: CowArc::Borrowed(arg),
            },
            Self::App {
                head,
                args: CowArc::Borrowed(args),
            } if head.is_static() => Self::App {
                head: head.const_clone(),
                args: CowArc::Borrowed(*args),
            },
            Self::Var(variable) if variable.is_static() => Self::Var(variable.const_clone()),
            _ => panic!("not const formula"),
        }
    }
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

static FULL_VARS: bool = false;
impl<'a> From<&'a RecFOFormula> for SExpr<'a> {
    fn from(value: &'a RecFOFormula) -> Self {
        use SExpr::*;
        match value {
            RecFOFormula::Quantifier { head, vars, arg } => Group(vec![
                Atom(head),
                Group(vars.iter().map(|x| mk_var_sexpr(x)).collect()),
                Group(arg.iter().map(|x| Atom(x)).collect()),
            ]),
            RecFOFormula::App { head, args } => {
                Group(chain![[Atom(head)], args.iter().map(|x| Atom(x)),].collect())
            }
            RecFOFormula::Var(variable) => mk_var_sexpr(variable),
        }
    }
}

#[inline]
fn mk_var_sexpr<'a>(v: &'a Variable) -> SExpr<'a> {
    use SExpr::*;
    if FULL_VARS { Atom(v) } else { AtomDebug(v) }
}

impl Default for RecFOFormula {
    fn default() -> Self {
        Self::App {
            head: TRUE.clone(),
            args: Default::default(),
        }
    }
}
impl Formula for RecFOFormula {
    type Var = Variable;

    type Fun = Function;

    type Quant = RecFOFormulaQuant;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Quantifier { head, vars, arg } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuant::new(head, vars.as_owned())),
                args: MIter::One(arg.as_owned().into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head.clone()),
                args: MIter::Many(args.as_owned().into_iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl<'b> Formula for &'b RecFOFormula {
    type Var = &'b Variable;

    type Fun = &'b Function;

    type Quant = RecFOFormulaQuantRef<'b>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Quantifier { head, vars, arg } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuantRef::new(*head, vars.as_ref())),
                args: MIter::One(arg.iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head),
                args: MIter::Many(args.iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}
impl From<MSmtFormula> for RecFOFormula {
    fn from(value: MSmtFormula) -> Self {
        // TODO: find such that

        #[allow(unreachable_patterns)]
        match value {
            SmtFormula::Var(var) => Self::Var(var),
            SmtFormula::Fun(fun, args) => RecFOFormula::App {
                head: fun,
                args: args.into_iter().map_into().collect(),
            },
            SmtFormula::Forall(vars, formula) => {
                let arg = mk_cowarc![Self::from(*formula)];
                Self::Quantifier {
                    head: FOBinder::Forall,
                    vars: vars.into(),
                    // sorts,
                    arg,
                }
            }
            SmtFormula::Exists(vars, formula) => {
                let arg = mk_cowarc![Self::from(*formula)];
                Self::Quantifier {
                    head: FOBinder::Exists,
                    vars: vars.into(),
                    arg,
                }
            }
            SmtFormula::True => Self::app(TRUE.clone(), vec![]),
            SmtFormula::False => Self::app(FALSE.clone(), vec![]),
            SmtFormula::And(args) => Self::fold(&AND, args.into_iter().map_into(), None, false),
            SmtFormula::Or(args) => Self::fold(&OR, args.into_iter().map_into(), None, false),
            SmtFormula::Eq(args) => Self::fold(&EQ, args.into_iter().map_into(), None, true),
            SmtFormula::Neq(args) => !Self::fold(&EQ, args.into_iter().map_into(), None, true),
            SmtFormula::Not(arg) => !Self::from(*arg),
            SmtFormula::Implies(a, b) => Self::from(*a) >> Self::from(*b),
            SmtFormula::Ite(c, l, r) => {
                Self::app(BITE.clone(), [c, l, r].map(|x| Self::from(*x)).into())
            }
            _ => unimplemented!(),
        }
    }
}

impl Not for RecFOFormula {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::app(NOT.clone(), vec![self])
    }
}

impl BitAnd for RecFOFormula {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::app(AND.clone(), vec![self, rhs])
    }
}

impl BitOr for RecFOFormula {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::app(OR.clone(), vec![self, rhs])
    }
}

impl Shr for RecFOFormula {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Self::app(IMPLIES.clone(), vec![self, rhs])
    }
}

pub trait QuantifierTranslator {
    fn try_translate(&self, f: &RecFOFormula) -> Option<RecFOFormula>;
}

#[derive(Builder)]
pub struct PreSmtRecFOFormula<'a, U> {
    formula: Cow<'a, RecFOFormula>,
    translator: &'a U,
}

/// Shortcut to keep signatures sane
pub type PreSmtRecFOFormulaF<'a, U> = PreSmtRecFOFormulaBuilder<
    'a,
    U,
    pre_smt_rec_f_o_formula_builder::SetFormula<pre_smt_rec_f_o_formula_builder::Empty>,
>;

impl<'a, U: QuantifierTranslator> TryFrom<PreSmtRecFOFormula<'a, U>> for MSmtFormula {
    type Error = RecFOFormula;

    fn try_from(
        PreSmtRecFOFormula {
            formula,
            translator,
        }: PreSmtRecFOFormula<'a, U>,
    ) -> Result<Self, Self::Error> {
        let propagate = |f: &RecFOFormula| f.as_pre_smt().translator(translator).build().try_into();
        let restult = match formula.as_ref() {
            RecFOFormula::Var(variable) => Ok(Self::Var(variable.clone())),
            RecFOFormula::App { head, args } => match head.as_smt_head() {
                Some(h) => {
                    let args = args.iter().map(propagate).try_collect()?;
                    Ok(match h {
                        SmtHead::True => Self::True,
                        SmtHead::False => Self::False,
                        SmtHead::And => Self::And(args),
                        SmtHead::Or => Self::Or(args),
                        SmtHead::Eq => Self::Eq(args),
                        SmtHead::Neq => Self::Neq(args),
                        SmtHead::Not => {
                            let [arg] = TryInto::<[_; _]>::try_into(args)
                                .map_err(|_| formula.into_owned())?
                                .map(Box::new);
                            Self::Not(arg)
                        }
                        SmtHead::Implies => {
                            let [a1, a2] = TryInto::<[_; _]>::try_into(args)
                                .map_err(|_| formula.into_owned())?
                                .map(Box::new);
                            Self::Implies(a1, a2)
                        }
                        SmtHead::If => {
                            let [c, l, r] = TryInto::<[_; _]>::try_into(args)
                                .map_err(|_| formula.into_owned())?
                                .map(Box::new);
                            Self::Ite(c, l, r)
                        }
                    })
                }
                None => {
                    let args = args.iter().map(propagate).try_collect()?;
                    Ok(Self::Fun(head.clone(), args))
                }
            },
            RecFOFormula::Quantifier { head, vars, arg } => match head {
                FOBinder::Exists => {
                    Ok(Self::Exists(vars.as_owned(), Box::new(propagate(&arg[0])?)))
                }
                FOBinder::Forall => {
                    Ok(Self::Forall(vars.as_owned(), Box::new(propagate(&arg[0])?)))
                }
                FOBinder::FindSuchThat => match translator.try_translate(&formula) {
                    Some(f) => propagate(&f),
                    None => Err(formula.into_owned()),
                },
            },
        };

        #[cfg(debug_assertions)]
        if let Err(f) = &restult {
            use log::error;

            error!("fail to translate to smt\n{f}")
        }
        restult
    }
}

impl Display for RecFOFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        super::sexpr::SExpr::from(self).fmt(f)
    }
}

impl Debug for RecFOFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[cfg(feature = "verbose")]
        {
            match self {
                Self::Quantifier { head, vars, arg } => f
                    .debug_struct("Quantifier")
                    .field("head", head)
                    .field("vars", vars)
                    .field("arg", arg)
                    .finish(),
                Self::App { head, args } => f
                    .debug_struct("App")
                    .field("head", head)
                    .field("args", args)
                    .finish(),
                Self::Var(arg0) => f.debug_tuple("Var").field(arg0).finish(),
            }
        }

        #[cfg(not(feature = "verbose"))]
        {
            Display::fmt(&self, f)
        }
    }
}

// =========================================================
// ====================== Steel API ========================
// =========================================================

impl RecFOFormula {
    // TODO: find such that
    fn steel_binder(head: FOBinder, vars: Vec<Variable>, arg: Vec<RecFOFormula>) -> Self {
        assert!(
            vars.iter().all(Variable::has_smt_sort),
            "Variable must have valid smt sort, see Variable::has_smt_sort"
        );
        let vars = vars.into_iter().map_into().collect();
        Self::Quantifier {
            head,
            vars,
            arg: arg.into(),
        }
    }

    fn steel_app(head: Function, args: Vec<RecFOFormula>) -> Result<Self, SteelErr> {
        let ret = Self::App {
            head,
            args: args.into(),
        };
        let Self::App { head, args } = &ret else {
            unreachable!()
        };

        // checks
        if head.arity() != args.len() {
            return Err(SteelErr::new(
                rerrs::ErrorKind::ArityMismatch,
                format!("expect {} got {}: ({ret})", head.arity(), args.len()),
            ));
        }

        for (i, (arg, &s)) in izip!(args.iter(), head.signature.inputs.iter()).enumerate() {
            econtinue_let!(let Some(s2) = arg.try_get_sort());
            if s2 != s {
                return Err(SteelErr::new(
                    rerrs::ErrorKind::TypeMismatch,
                    format!("epxected {s} got {s2} in argument {i:} of {ret}"),
                ));
            }
        }

        Ok(ret)
    }

    fn steel_var(var: Variable) -> Self {
        Self::Var(var)
    }

    fn steel_is_var(f: RecFOFormula) -> bool {
        matches!(f, Self::Var(_))
    }

    fn steel_get_sort(&self) -> Option<Sort> {
        self.try_get_sort()
    }

    fn steel_and(args: Vec<Self>) -> Self {
        Self::and(args)
    }

    fn steel_or(args: Vec<Self>) -> Self {
        Self::or(args)
    }

    fn steel_tuple(args: Vec<Self>) -> Self {
        args.into_iter()
            .rev()
            .reduce(|acc, e| rexp!((TUPLE #acc #e)))
            .unwrap_or(rexp!(EMPTY))
    }
}

impl Registerable for RecFOFormula {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        module
            .register_fn("mk-binderf", Self::steel_binder)
            .register_fn("mk-appf", Self::steel_app)
            .register_fn("mk-varf", Self::steel_var)
            .register_value("existsf", FOBinder::Exists.into_steelval().unwrap())
            .register_value("forallf", FOBinder::Forall.into_steelval().unwrap())
            .register_value("findstf", FOBinder::FindSuchThat.into_steelval().unwrap())
            .register_fn("is-varf", Self::steel_is_var)
            .register_fn("get-sort", Self::steel_get_sort)
            .register_type::<Self>("Formula?")
            .register_fn("string-of-formula", |f: RecFOFormula| format!("{f}"))
            .register_fn("cand", Self::steel_and)
            .register_fn("cor", Self::steel_or)
            .register_fn("tuple", Self::steel_tuple)
    }
}
