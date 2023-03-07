use itertools::Itertools;

use crate::smt::smt::SmtFormula;

use super::{
    formula::{RichFormula, Variable},
    function::Function,
    quantifier::Quantifier,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionShortcuter {
    eq: Function,
    and: Function,
    or: Function,
    implies: Function,
    true_f: Function,
    false_f: Function,
    not: Function,
}
pub struct FunctionShortcuterBuilder {
    pub eq: Function,
    pub and: Function,
    pub or: Function,
    pub implies: Function,
    pub true_f: Function,
    pub false_f: Function,
    pub not: Function,
}

impl From<FunctionShortcuterBuilder> for FunctionShortcuter {
    fn from(f: FunctionShortcuterBuilder) -> Self {
        let FunctionShortcuterBuilder {
            eq,
            and,
            or,
            implies,
            true_f,
            false_f,
            not,
        } = f;
        FunctionShortcuter {
            eq,
            and,
            or,
            implies,
            true_f,
            false_f,
            not,
        }
    }
}

pub trait FormulaUser<A> {
    fn truef(&self) -> A;
    fn falsef(&self) -> A;
    fn eqf(&self, a: A, b: A) -> A;
    fn neqf(&self, a: A, b: A) -> A;
    fn andf(&self, a: A, b: A) -> A;
    fn orf(&self, a: A, b: A) -> A;
    fn negf(&self, a: A) -> A;
    fn impliesf(&self, a: A, b: A) -> A;
    fn forallf(&self, vars: Vec<Variable>, f: A) -> A;
    fn existsf(&self, vars: Vec<Variable>, f: A) -> A;
    fn varf(&self, var: Variable) -> A;
    fn funf(&self, fun: Function, args: impl IntoIterator<Item = A>) -> A;

    /// multiple eq
    fn meqf(&self, args: impl IntoIterator<Item = A>) -> A;
    /// multiple neq
    fn mneqf(&self, args: impl IntoIterator<Item = A>) -> A;
    /// multiple and
    fn mandf(&self, args: impl IntoIterator<Item = A>) -> A;
    /// multiple or
    fn morf(&self, args: impl IntoIterator<Item = A>) -> A;

    fn forallff<V, F, const N: usize>(&self, vars: [V; N], f: F) -> A
    where
        V: Into<Variable>,
        F: Fn([A; N]) -> A,
    {
        let vars = vars.map(Into::into);
        debug_assert!(vars.iter().map(|v| v.id).duplicates().next().is_none());
        let vars_2 = vars.clone().map(|v| self.varf(v));
        self.forallf(vars.into(), f(vars_2))
    }

    fn existsff<V, F, const N: usize>(&self, vars: [V; N], f: F) -> A
    where
        V: Into<Variable>,
        F: Fn([A; N]) -> A,
    {
        let vars = vars.map(Into::into);
        let vars_2 = vars.clone().map(|v| self.varf(v));
        self.existsf(vars.into(), f(vars_2))
    }
}

pub(crate) trait HasShortcut {
    fn get_function_shortcut(&self) -> &FunctionShortcuter;
}

impl FormulaUser<RichFormula> for FunctionShortcuter {
    fn truef(&self) -> RichFormula {
        RichFormula::Fun(self.true_f.clone(), vec![])
    }

    fn falsef(&self) -> RichFormula {
        RichFormula::Fun(self.false_f.clone(), vec![])
    }

    fn eqf(&self, a: RichFormula, b: RichFormula) -> RichFormula {
        RichFormula::Fun(self.eq.clone(), vec![a, b])
    }

    fn neqf(&self, a: RichFormula, b: RichFormula) -> RichFormula {
        self.negf(RichFormula::Fun(self.eq.clone(), vec![a, b]))
    }

    fn andf(&self, a: RichFormula, b: RichFormula) -> RichFormula {
        RichFormula::Fun(self.and.clone(), vec![a, b])
    }

    fn orf(&self, a: RichFormula, b: RichFormula) -> RichFormula {
        RichFormula::Fun(self.or.clone(), vec![a, b])
    }

    fn negf(&self, a: RichFormula) -> RichFormula {
        RichFormula::Fun(self.not.clone(), vec![a])
    }

    fn impliesf(&self, a: RichFormula, b: RichFormula) -> RichFormula {
        RichFormula::Fun(self.implies.clone(), vec![a, b])
    }

    fn forallf(&self, vars: Vec<Variable>, f: RichFormula) -> RichFormula {
        RichFormula::Quantifier(Quantifier::Forall { variables: vars }, vec![f])
    }

    fn existsf(&self, vars: Vec<Variable>, f: RichFormula) -> RichFormula {
        RichFormula::Quantifier(Quantifier::Exists { variables: vars }, vec![f])
    }

    fn varf(&self, var: Variable) -> RichFormula {
        RichFormula::Var(var)
    }

    fn funf(&self, fun: Function, args: impl IntoIterator<Item = RichFormula>) -> RichFormula {
        RichFormula::Fun(fun, args.into_iter().collect())
    }

    fn meqf(&self, args: impl IntoIterator<Item = RichFormula>) -> RichFormula {
        self.mandf(
            args.into_iter()
                .tuple_windows()
                .map(|(a, b)| self.eqf(a, b)),
        )
    }

    fn mneqf(&self, args: impl IntoIterator<Item = RichFormula>) -> RichFormula {
        self.negf(self.meqf(args))
    }

    fn mandf(&self, args: impl IntoIterator<Item = RichFormula>) -> RichFormula {
        let mut iter = args.into_iter();
        let fst = iter.next();
        if let Some(fst) = fst {
            iter.fold(fst, |acc, x| self.andf(acc, x))
        } else {
            self.truef()
        }
    }

    fn morf(&self, args: impl IntoIterator<Item = RichFormula>) -> RichFormula {
        let mut iter = args.into_iter();
        let fst = iter.next();
        if let Some(fst) = fst {
            iter.fold(fst, |acc, x| self.orf(acc, x))
        } else {
            self.falsef()
        }
    }
}

impl FormulaUser<SmtFormula> for FunctionShortcuter {
    fn truef(&self) -> SmtFormula {
        SmtFormula::Fun(self.true_f.clone(), vec![])
    }

    fn falsef(&self) -> SmtFormula {
        SmtFormula::Fun(self.false_f.clone(), vec![])
    }

    fn eqf(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        SmtFormula::Eq(vec![a, b])
    }

    fn neqf(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        SmtFormula::Eq(vec![a, b])
    }

    fn andf(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        SmtFormula::And(vec![a, b])
    }

    fn orf(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        SmtFormula::Or(vec![a, b])
    }

    fn negf(&self, a: SmtFormula) -> SmtFormula {
        SmtFormula::Fun(self.not.clone(), vec![a])
    }

    fn impliesf(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        SmtFormula::Fun(self.implies.clone(), vec![a, b])
    }

    fn forallf(&self, vars: Vec<Variable>, f: SmtFormula) -> SmtFormula {
        SmtFormula::Forall(vars, Box::new(f))
    }

    fn existsf(&self, vars: Vec<Variable>, f: SmtFormula) -> SmtFormula {
        SmtFormula::Exists(vars, Box::new(f))
    }

    fn varf(&self, var: Variable) -> SmtFormula {
        SmtFormula::Var(var)
    }

    fn funf(&self, fun: Function, args: impl IntoIterator<Item = SmtFormula>) -> SmtFormula {
        SmtFormula::Fun(fun, args.into_iter().collect())
    }

    fn meqf(&self, args: impl IntoIterator<Item = SmtFormula>) -> SmtFormula {
        SmtFormula::Eq(args.into_iter().collect())
    }

    fn mneqf(&self, args: impl IntoIterator<Item = SmtFormula>) -> SmtFormula {
        SmtFormula::Neq(args.into_iter().collect())
    }

    fn mandf(&self, args: impl IntoIterator<Item = SmtFormula>) -> SmtFormula {
        SmtFormula::And(args.into_iter().collect())
    }

    fn morf(&self, args: impl IntoIterator<Item = SmtFormula>) -> SmtFormula {
        SmtFormula::Or(args.into_iter().collect())
    }
}

macro_rules! impl_formula_user {
    ($a:ty) => {
        impl<T: HasShortcut> FormulaUser<$a> for T {
            fn truef(&self) -> $a {
                self.get_function_shortcut().truef()
            }

            fn falsef(&self) -> $a {
                self.get_function_shortcut().falsef()
            }

            fn eqf(&self, a: $a, b: $a) -> $a {
                self.get_function_shortcut().eqf(a, b)
            }

            fn neqf(&self, a: $a, b: $a) -> $a {
                self.get_function_shortcut().neqf(a, b)
            }

            fn andf(&self, a: $a, b: $a) -> $a {
                self.get_function_shortcut().andf(a, b)
            }

            fn orf(&self, a: $a, b: $a) -> $a {
                self.get_function_shortcut().orf(a, b)
            }

            fn negf(&self, a: $a) -> $a {
                self.get_function_shortcut().negf(a)
            }

            fn impliesf(&self, a: $a, b: $a) -> $a {
                self.get_function_shortcut().impliesf(a, b)
            }

            fn forallf(&self, vars: Vec<Variable>, f: $a) -> $a {
                self.get_function_shortcut().forallf(vars, f)
            }

            fn existsf(&self, vars: Vec<Variable>, f: $a) -> $a {
                self.get_function_shortcut().existsf(vars, f)
            }

            fn varf(&self, var: Variable) -> $a {
                self.get_function_shortcut().varf(var)
            }

            fn funf(&self, fun: Function, args: impl IntoIterator<Item = $a>) -> $a {
                self.get_function_shortcut().funf(fun, args)
            }

            fn meqf(&self, args: impl IntoIterator<Item = $a>) -> $a {
                self.get_function_shortcut().meqf(args)
            }

            fn mneqf(&self, args: impl IntoIterator<Item = $a>) -> $a {
                self.get_function_shortcut().mneqf(args)
            }

            fn mandf(&self, args: impl IntoIterator<Item = $a>) -> $a {
                self.get_function_shortcut().mandf(args)
            }

            fn morf(&self, args: impl IntoIterator<Item = $a>) -> $a {
                self.get_function_shortcut().morf(args)
            }
        }
    };
}

impl_formula_user!(RichFormula);
impl_formula_user!(SmtFormula);

// macro_rules! existsf {
//     ($ctx:expr; $($name:ident ! $i:literal : $sort:expr),*; $content:block) => {{
//         let f = |$($name),*| $content;
//         ctx.existsf(
//             vec![$(crate::formula::formula::Variable {id: $i, sort: $sort.clone()}),*],

//                 f($(ctx.varf(crate::formula::formula::Variable {id: $i, sort: $sort.clone()})),*)

//         )
//     }};
// }

// macro_rules! forallf {
//     ($ctx:expr; $($name:ident ! $i:literal : $sort:expr),*; $content:block) => {{
//         $ctx.forallff( [$(crate::formula::formula::Variable {id: $i, sort: $sort.clone()}),*], |[$($name),*]| $content)
//     }};
// }

// pub(crate) use {existsf, forallf};
