use std::borrow::Cow;
use std::fmt::Display;
use std::ops::{BitAnd, BitOr, Not, Shr};

use cryptovampire_smt::{IntoSmt, SmtFormula, SmtQuantifier, SortedVar, VarInner};
use egg::{Analysis, EGraph, Id, Language, PatternAst, RecExpr, Var};
use im_rc::HashSet;
use itertools::{Itertools, izip};
use logic_formula::egg::SimplLang;
use logic_formula::{Destructed, Formula, HeadSk};
use smallvec::SmallVec;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;
use utils::{dynamic_iter, ereturn_if, implvec, match_eq};

use crate::input::Registerable;
use crate::input::var::SVar;
use crate::terms::{AND, BITE, EQ, FALSE, Function, IMPLIES, NOT, OR, Sort, TRUE, convert_smt_var};
use crate::{Lang, LangVar};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Steel)]
pub enum RecFOFormula {
    Binder {
        head: FOBinder,
        vars: Vec<Var>,
        sorts: Vec<Sort>,
        arg: Box<RecFOFormula>,
    },
    App {
        head: Function,
        args: Vec<RecFOFormula>,
    },
    Var(Var),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Steel)]
pub enum FOBinder {
    Forall,
    Exists,
}

impl RecFOFormula {
    pub fn bind(kind: FOBinder, vars: Vec<Var>, sorts: Vec<Sort>, arg: RecFOFormula) -> Self {
        assert_eq!(vars.len(), sorts.len());
        Self::Binder {
            head: kind,
            vars,
            sorts,
            arg: Box::new(arg),
        }
    }

    pub fn app(fun: Function, args: Vec<Self>) -> Self {
        Self::App { head: fun, args }
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
            RecFOFormula::Binder { arg, .. } => arg.try_evaluate(),
            _ => None,
        }
    }

    fn as_recexp_inner(&self, res: &mut Vec<LangVar>) -> Option<usize> {
        match self {
            RecFOFormula::Binder { .. } => None,
            RecFOFormula::Var(var) => {
                res.push(egg::ENodeOrVar::Var(*var));
                Some(res.len() - 1)
            }
            RecFOFormula::App { head, args } => {
                let args: Option<SmallVec<_>> = args
                    .iter()
                    .map(|arg| arg.as_recexp_inner(res).map(egg::Id::from))
                    .collect();
                let head = SimplLang {
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

        super::formula_utils::pull_from_egraph_inner(
            egraph,
            id,
            &mut id_buffer,
            &mut recexpr_buffer,
        )?;

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
            RecFOFormula::Binder { .. } => Some(Sort::Bool),
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
    pub fn subst(&self, subst: &[(Var, Self)]) -> Self {
        self.inner_subst(subst, &Default::default())
    }

    /// helper function for [Self::subst]
    fn inner_subst(&self, subst: &[(Var, Self)], bvars: &HashSet<Var>) -> Self {
        match self {
            Self::Binder {
                head,
                vars,
                sorts,
                arg,
            } => {
                let mut bvars = bvars.clone();
                bvars.extend(vars.iter().cloned());
                Self::Binder {
                    head: *head,
                    vars: vars.clone(),
                    sorts: sorts.clone(),
                    arg: Box::new(arg.inner_subst(subst, &bvars)),
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
    // ================== specific builders ====================
    // =========================================================

    #[allow(non_snake_case)]
    pub fn True() -> Self {
        Self::app(TRUE.clone(), vec![])
    }

    #[allow(non_snake_case)]
    pub fn False() -> Self {
        Self::app(FALSE.clone(), vec![])
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

    pub fn optimised_binder(
        kind: FOBinder,
        vars: implvec!(Var),
        sorts: implvec!(Sort),
        arg: RecFOFormula,
    ) -> Self {
        ereturn_if!(arg.is_true() || arg.is_false(), arg);
        let free_vars: Vec<Var> = (&arg).free_vars_iter().unique().collect();

        let (vars, sorts): (Vec<_>, Vec<_>) = izip!(vars.into_iter(), sorts.into_iter())
            .filter(|(v, _)| free_vars.as_slice().contains(v))
            .unzip();

        ereturn_if!(vars.is_empty(), arg);
        Self::bind(kind, vars, sorts, arg)
    }
}

impl From<&[LangVar]> for RecFOFormula {
    fn from(v: &[LangVar]) -> Self {
        let Destructed { head, args } = v.destruct();
        match head {
            HeadSk::Var(v) => Self::Var(v),
            HeadSk::Fun(head) => Self::App {
                head,
                args: args.map_into().collect(),
            },
            HeadSk::Quant(_) => unreachable!(),
        }
    }
}

impl From<&RecExpr<LangVar>> for RecFOFormula {
    fn from(value: &RecExpr<LangVar>) -> Self {
        let x: &[_] = value;
        x.into()
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
            args: vec![],
        }
    }
}

pub struct RecFOFormulaQuant<'a> {
    pub quantifier: FOBinder,
    pub vars: Cow<'a, [Var]>,
    pub sorts: Cow<'a, [Sort]>,
}

impl<'a> RecFOFormulaQuant<'a> {
    pub fn new(quantifier: FOBinder, vars: Cow<'a, [Var]>, sorts: Cow<'a, [Sort]>) -> Self {
        Self {
            quantifier,
            vars,
            sorts,
        }
    }
}

impl Formula for RecFOFormula {
    type Var = egg::Var;

    type Fun = Function;

    type Quant = RecFOFormulaQuant<'static>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Binder {
                head,
                vars,
                sorts,
                arg,
            } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuant::new(head, vars.into(), sorts.into())),
                args: MIter::One([*arg].into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head.clone()),
                args: MIter::Many(args.into_iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl<'b> Formula for &'b RecFOFormula {
    type Var = egg::Var;

    type Fun = &'b Function;

    type Quant = RecFOFormulaQuant<'b>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Binder {
                head,
                vars,
                sorts,
                arg,
            } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuant::new(
                    *head,
                    vars.as_slice().into(),
                    sorts.as_slice().into(),
                )),
                args: MIter::One([arg.as_ref()].into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head),
                args: MIter::Many(args.iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(*var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl<'a> logic_formula::Bounder<Var> for RecFOFormulaQuant<'a> {
    fn bounds(&self) -> impl Iterator<Item = Var> {
        self.vars.iter().copied()
    }
}

impl From<SmtFormula<Sort, Function>> for RecFOFormula {
    fn from(value: SmtFormula<Sort, Function>) -> Self {
        #[allow(unreachable_patterns)]
        match value {
            SmtFormula::Var(var) => Self::Var(convert_smt_var(var)),
            SmtFormula::Fun(fun, args) => RecFOFormula::App {
                head: fun,
                args: args.into_iter().map_into().collect(),
            },
            SmtFormula::Forall(vars, formula) => {
                let (vars, sorts) = vars
                    .into_iter()
                    .map(|SortedVar { var, sort }| (convert_smt_var(var), sort))
                    .unzip();
                let arg = Box::new(Self::from(*formula));
                Self::Binder {
                    head: FOBinder::Forall,
                    vars,
                    sorts,
                    arg,
                }
            }
            SmtFormula::Exists(vars, formula) => {
                let (vars, sorts) = vars
                    .into_iter()
                    .map(|SortedVar { var, sort }| (convert_smt_var(var), sort))
                    .unzip();
                let arg = Box::new(Self::from(*formula));
                Self::Binder {
                    head: FOBinder::Exists,
                    vars,
                    sorts,
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

impl IntoSmt<Sort> for RecFOFormula {
    fn convert_var(var: egg::Var) -> VarInner {
        match var.expose() {
            egg::VarExposed::Sym(s) => VarInner::Str(s.into()),
            egg::VarExposed::Num(n) => VarInner::Int(n as cryptovampire_smt::uvar),
        }
    }

    fn convert_quant(
        RecFOFormulaQuant {
            quantifier,
            vars,
            sorts,
        }: Self::Quant,
    ) -> SmtQuantifier<Sort> {
        assert!(
            !sorts.iter().any(Sort::is_any),
            "`Any` is not allowed in smt"
        );
        let vars = izip!(vars.iter(), sorts.iter())
            .map(|(&var, &sort)| SortedVar {
                var: Self::convert_var(var),
                sort,
            })
            .collect_vec();
        match quantifier {
            FOBinder::Forall => SmtQuantifier::Forall(vars),
            FOBinder::Exists => SmtQuantifier::Exists(vars),
        }
    }

    fn as_head(fun: &Self::Fun) -> Option<cryptovampire_smt::SmtHead> {
        fun.as_smt_head()
    }
}

impl Display for RecFOFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let smt = self.clone().into_smt();
        write!(f, "{smt}")
    }
}

impl FOBinder {
    /// The value taken by the quantifier on an empty set
    ///
    /// ```text
    /// \exists => false
    /// \forall => true
    /// ```
    pub fn on_empty(&self) -> bool {
        match self {
            FOBinder::Forall => true,
            FOBinder::Exists => false,
        }
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

    fn steel_binder(head: FOBinder, vars: Vec<SVar>, sorts: Vec<Sort>, arg: RecFOFormula) -> Self {
        // let (vars, sorts): (Vec<_>, Vec<_>) =
        //     vars.into_iter().map(|(v, s)| (Var::from(v), s)).unzip();
        let vars = vars.into_iter().map_into().collect();
        Self::Binder {
            head,
            vars,
            sorts,
            arg: Box::new(arg),
        }
    }

    fn steel_app(head: Function, args: Vec<RecFOFormula>) -> Self {
        Self::App { head, args }
    }

    fn steel_var(var: SVar) -> Self {
        Self::Var(var.into())
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
