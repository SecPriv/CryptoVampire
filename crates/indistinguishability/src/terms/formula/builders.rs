use std::ops::{BitAnd, BitOr, Not, Shr};

use itertools::Itertools;
use quarck::CowArc;
use utils::{ereturn_if, ereturn_let, implvec};

use super::Formula;
use crate::rexp;
use crate::terms::{AND, FALSE, FOBinder, Function, IMPLIES, NOT, OR, TRUE, Variable};

// =========================================================
// ================== specific builders ====================
// =========================================================
impl Formula {
    pub fn bind(kind: FOBinder, vars: Vec<Variable>, args: implvec!(Formula)) -> Self {
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
    pub fn optimised_binder(_kind: FOBinder, _vars: implvec!(Variable), _arg: Formula) -> Self {
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

    fn split_conjunction_inner(self, uqvar: &[Variable], condition: Self) -> Vec<Self> {
        match self {
            Self::Quantifier {
                head: FOBinder::Forall,
                vars,
                arg,
            } => {
                let vars = {
                    let mut tmp = uqvar.to_vec();
                    tmp.extend_from_slice(&vars);
                    tmp
                };
                arg[0].clone().split_conjunction_inner(&vars, condition)
            }
            Self::App { head, args } if head == AND => {
                let (a, b) = args.iter().cloned().collect_tuple().unwrap();
                [a, b]
                    .into_iter()
                    .flat_map(|x| x.split_conjunction_inner(uqvar, condition.clone()))
                    .collect()
            }
            Self::App { head, args } if head == IMPLIES => {
                let (a, b) = args.iter().cloned().collect_tuple().unwrap();
                b.split_conjunction_inner(uqvar, condition & a)
            }
            x => {
                let vars = uqvar.iter().cloned();
                vec![rexp!((forall #vars (=> #condition #x)))]
            }
        }
    }

    pub fn split_conjunction(self) -> Vec<Self> {
        self.split_conjunction_inner(&[], rexp!(true))
    }
}
impl Not for Formula {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::app(NOT.clone(), vec![self])
    }
}

impl BitAnd for Formula {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::app(AND.clone(), vec![self, rhs])
    }
}

impl BitOr for Formula {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::app(OR.clone(), vec![self, rhs])
    }
}

impl Shr for Formula {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Self::app(IMPLIES.clone(), vec![self, rhs])
    }
}
