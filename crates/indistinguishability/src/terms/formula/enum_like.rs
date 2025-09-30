use std::borrow::Cow;
use std::fmt::Display;
use std::ops::{BitAnd, BitOr, Not, Shr};

use cryptovampire_smt::{IntoSmt, SmtFormula, SmtQuantifier, SortedVar};
use egg::{Analysis, EGraph, Id, Language, PatternAst, RecExpr};
use itertools::{Itertools, chain, izip};
use logic_formula::{Destructed, Formula, HeadSk};
use rpds::HashTrieSet;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use steel::core::labels::fresh;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;
use utils::{dynamic_iter, ereturn_if, implvec, match_eq};

use super::{FOBinder, RecFOFormulaQuant};
use crate::input::Registerable;
use crate::terms::formula::egg::EggLanguage;
use crate::terms::formula::{FormulaLike, RecFOFormulaQuantRef, sort_list};
use crate::terms::utils::{mk_var, pull_from_egraph};
use crate::terms::{
    AND, BITE, CONS, EQ, FALSE, Function, IMPLIES, LAMBDA_O, LAMBDA_S, NIL, NOT, OR, Sort, TRUE,
    Variable,
};
use crate::{Lang, LangVar, MSmtFormula, MSmtParam, fresh};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Steel)]
pub enum RecFOFormula {
    Quantifier {
        head: FOBinder,
        vars: cow![Variable],
        arg: cow![RecFOFormula],
    },
    App {
        head: Function,
        args: cow![RecFOFormula],
    },
    Var(Variable),
}
impl RecFOFormula {
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
            RecFOFormula::Quantifier { arg, .. } => todo!(),
            _ => None,
        }
    }

    fn as_recexp_inner(&self, res: &mut Vec<LangVar>) -> Option<usize> {
        match self {
            RecFOFormula::Quantifier { .. } => None,
            RecFOFormula::Var(var) => {
                res.push(egg::ENodeOrVar::Var(var.as_egg()));
                Some(res.len() - 1)
            }
            RecFOFormula::App { head, args } => {
                let args: Option<SmallVec<_>> = args
                    .iter()
                    .map(|arg| arg.as_recexp_inner(res).map(egg::Id::from))
                    .collect();
                let head = crate::Lang {
                    head: head.clone(),
                    args: args?,
                };
                res.push(egg::ENodeOrVar::ENode(head));
                Some(res.len() - 1)
            }
        }
    }

    pub fn as_recexp(&self) -> Option<PatternAst<Lang>> {
        let mut ret = Vec::new();
        self.as_recexp_inner(&mut ret)?;
        Some(ret.into())
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

    pub fn try_from_id<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> Option<Self> {
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

    // =========================================================
    // ===================== conversion ========================
    // =========================================================

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
                        sort_list::try_get(Self::from(sort_exp))
                            .expect("a list of sorts as first arg")
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
                                bound_variables,
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
                        vars: Cow::Owned(vars),
                        arg: Cow::Owned(args),
                    }
                } else {
                    // a regular function
                    let args = Itertools::zip_eq(head.signature.inputs.iter(), args).map(
                        |(&sort, arg)| {
                            Self::inner_from_egg(
                                arg,
                                bound_variables,
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

    pub fn as_egg<L: EggLanguage>(&self) -> Vec<L> {
        let mut out = Vec::new();
        self.as_egg_inner(&mut out, Default::default(), 0);
        out
    }

    fn as_egg_inner<'a, L: EggLanguage>(
        &'a self,
        out: &mut Vec<L>,
        bvars: rpds::HashTrieMap<&'a Variable, usize>,
        size: usize,
    ) -> usize {
        match self {
            Self::Quantifier { head, vars, arg } => {
                debug_assert_eq!(bvars.iter().len(), size);
                let mut bvars = bvars;
                for (i, var) in vars.iter().enumerate() {
                    bvars = bvars.insert(var, size + i);
                }
                let size = size + vars.len();

                let mut nargs = Vec::with_capacity(arg.len() + 1);
                nargs.push(mk_list(out, vars.iter().map(|v| v.get_sort().unwrap())));
                nargs.extend(arg.iter().map(|arg| arg.as_egg_inner(out, bvars, size)));

                let head = head.as_function().cloned().unwrap();
                let nargs = nargs.into_iter().map(Id::from);
                out.push(L::mk_fun_application(head, nargs));
            }
            Self::App { head, args } => {
                let args = args
                    .iter()
                    .map(|arg| arg.as_egg_inner(out, bvars, size))
                    .map(Id::from)
                    .collect_vec();
                out.push(L::mk_fun_application(head.clone(), args));
            }
            Self::Var(variable) => match bvars.get(variable) {
                Some(i) => {
                    out.extend(mk_bound_var(*i));
                }
                None => out.push(L::mk_variable(variable)),
            },
        };

        out.len() - 1
    }

    // =========================================================
    // ================== specific builders ====================
    // =========================================================
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
        Self::constant(TRUE.const_clone().unwrap())
    }

    #[allow(non_snake_case)]
    pub fn False() -> Self {
        Self::constant(FALSE.const_clone().unwrap())
    }

    pub fn and(args: implvec!(Self)) -> Self {
        let mut ret = Self::True();
        for c in args.into_iter().filter(|x| !x.is_true()).unique() {
            ereturn_if!(c.is_false(), Self::False());
            ret = Self::app(AND.clone(), vec![c, ret]);
        }
        ret
    }

    pub fn or(args: implvec!(Self)) -> Self {
        let mut ret = Self::False();
        for c in args.into_iter().filter(|x| !x.is_false()).unique() {
            ereturn_if!(c.is_true(), Self::True());
            ret = Self::app(OR.clone(), vec![c, ret]);
        }
        ret
    }

    pub fn optimised_binder(kind: FOBinder, vars: implvec!(Variable), arg: RecFOFormula) -> Self {
        todo!()
        // ereturn_if!(arg.is_true() || arg.is_false(), arg);
        // let free_vars: Vec<Variable> = (&arg).free_vars_iter().unique().collect();

        // let (vars, sorts): (Vec<_>, Vec<_>) = izip!(vars.into_iter(), sorts.into_iter())
        //     .filter(|(v, _)| free_vars.as_slice().contains(v))
        //     .unzip();

        // ereturn_if!(vars.is_empty(), arg);
        // todo!("fixme");
        // Self::bind(kind, vars, sorts, [arg])
    }

    /// Makes a constant
    pub const fn constant(head: Function) -> Self {
        Self::App {
            head,
            args: Cow::Borrowed(&[]),
        }
    }

    pub const fn mk_const_app(head: Function, args: &'static [Self]) -> Self {
        Self::App {
            head,
            args: Cow::Borrowed(args),
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
            vars: Cow::Borrowed(vars),
            arg: Cow::Borrowed(arg),
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

impl TryFrom<RecFOFormula> for RecExpr<LangVar> {
    type Error = ();

    fn try_from(value: RecFOFormula) -> Result<Self, Self::Error> {
        match value.as_recexp() {
            Some(x) => Ok(x),
            None => Err(()),
        }
    }
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
                head: HeadSk::Quant(RecFOFormulaQuant::new(head, vars.into_owned())),
                args: MIter::One(arg.into_owned().into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head.clone()),
                args: MIter::Many(args.into_owned().into_iter()),
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
                let arg = mk_cow![Self::from(*formula)];
                Self::Quantifier {
                    head: FOBinder::Forall,
                    vars,
                    // sorts,
                    arg,
                }
            }
            SmtFormula::Exists(vars, formula) => {
                let arg = mk_cow![Self::from(*formula)];
                Self::Quantifier {
                    head: FOBinder::Exists,
                    vars,
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

impl IntoSmt<MSmtParam> for RecFOFormula {
    fn convert_var(var: Variable) -> Variable {
        var
    }

    fn convert_quant(
        RecFOFormulaQuant { quantifier, vars }: Self::Quant,
    ) -> SmtQuantifier<MSmtParam> {
        assert!(
            vars.iter().all(Variable::has_smt_sort),
            "Variable must have valid smt sort, see Variable::has_smt_sort"
        );
        match quantifier {
            FOBinder::Forall => SmtQuantifier::Forall(vars),
            FOBinder::Exists => SmtQuantifier::Exists(vars),
            _ => todo!(),
        }
    }

    fn as_head(fun: &Self::Fun) -> Option<cryptovampire_smt::SmtHead> {
        fun.as_smt_head()
    }

    fn convert_function(fun: Function) -> Function {
        fun
    }
}

impl Display for RecFOFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let smt = self.clone().into_smt();
        write!(f, "{smt}")
    }
}
// =========================================================
// ====================== Steel API ========================
// =========================================================

impl RecFOFormula {
    /// Turns self into a [PatternAst] but errors out with [steel]'s error instead of [Option]
    pub fn steel_maybe_as_recexp(&self) -> ::steel::rvals::Result<PatternAst<Lang>> {
        match self.as_recexp() {
            Some(patt) => Ok(patt),
            None => Err(::steel::SteelErr::new(
                ::steel::rerrs::ErrorKind::ConversionError,
                "could convert into RecExpr. Did you use quantifiers?".to_string(),
            )),
        }
    }

    // TODO: find such that
    fn steel_binder(head: FOBinder, vars: Vec<Variable>, arg: RecFOFormula) -> Self {
        assert!(
            vars.iter().all(Variable::has_smt_sort),
            "Variable must have valid smt sort, see Variable::has_smt_sort"
        );
        let vars = vars.into_iter().map_into().collect();
        Self::Quantifier {
            head,
            vars,
            arg: mk_cow![arg],
        }
    }

    fn steel_app(head: Function, args: Vec<RecFOFormula>) -> Self {
        Self::App {
            head,
            args: mk_cow!(@ args),
        }
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
            .register_fn("is-varf", Self::steel_is_var)
            .register_fn("get-sort", Self::steel_get_sort)
            .register_type::<Self>("Formula?")
            .register_fn("print_formula", |f: RecFOFormula| println!("this: {f}"))
    }
}

fn mk_bound_var<L: EggLanguage>(depth: usize) -> impl Iterator<Item = L> {
    chain![
        ::std::iter::once(L::mk_fun_application(LAMBDA_O.clone(), [])),
        (0..depth).map(|i| L::mk_fun_application(LAMBDA_S.clone(), [Id::from(i)]))
    ]
}

fn mk_list<L: EggLanguage>(out: &mut Vec<L>, sorts: implvec!(Sort)) -> usize {
    let sorts = sorts.into_iter();
    let mut i = out.len();
    out.reserve(sorts.size_hint().0 * 2 + 1);
    out.push(L::mk_fun_application(NIL, []));

    for sort in sorts {
        let sort = sort.as_function().unwrap();
        out.push(EggLanguage::mk_fun_application(sort.clone(), []));
        out.push(EggLanguage::mk_fun_application(
            CONS.clone(),
            [i, i + 1].map(Id::from),
        ));
        i += 2
    }
    i
}
