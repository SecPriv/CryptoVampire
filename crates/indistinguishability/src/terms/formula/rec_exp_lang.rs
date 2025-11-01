use std::collections::linked_list::IntoIter;
use std::default;
use std::num::{NonZeroU32, NonZeroUsize};
use std::ops::Deref;
use std::rc::Rc;

use egg::{ENodeOrVar, Id, RecExpr, Var};
use itertools::{Itertools, izip};
use logic_formula::{Destructed, Formula, HeadSk};
use steel::parser::kernel;
use utils::dynamic_iter;

use crate::terms::formula::{FormulaLike, RecFOFormulaQuant, sort_list};
use crate::terms::{FOBinder, Function, LAMBDA_O, LAMBDA_S, RecFOFormula, Sort};
use crate::utils::LightClone;
use crate::{Lang, LangVar};

/// This is a wrapper around a [RecExpr] that let us iterate over it using
/// [Formula].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RecExprIter<'a, L> {
    exp: &'a [L],
    vars: VariablesHelper,
}

impl<'a, L> Deref for RecExprIter<'a, L> {
    type Target = &'a [L];

    fn deref(&self) -> &Self::Target {
        &self.exp
    }
}

impl<'a, L: AsLangVar> RecExprIter<'a, L> {
    /// Creates a new `RecExprLang` with an empty variable list.
    ///
    /// *complexity*: `O(n)`
    pub fn new(exp: &'a [L]) -> Self {
        Self {
            exp,
            vars: VariablesHelper::new(exp),
        }
    }

    // pub fn get_min_var(&self) -> u32 {
    //     let Self { exp, vars } = self;
    //     Self::get_min_var_ref(exp, vars)
    // }

    // fn get_min_var_ref(exp: &'a [L], vars: &DeBruijnQueue) -> u32 {
    //     1 +
    //     // match

    //     match vars.peek() {
    //         // if there is a last variable, then it's the highest one
    //         Some(&v) => v,
    //         // otherwise we look in `exp`
    //         None => L::egg_free_vars(exp)
    //             .filter_map(|v| Var::as_u32(&v))
    //             .max()
    //             .unwrap_or(0),
    //     }
    // }
}

#[derive(Debug, Clone, Copy)]
enum LangVarLike<'a> {
    Var(u32),
    App { head: &'a Function, args: &'a [Id] },
}

trait AsLangVar: Sized {
    fn as_lang_var(&self) -> LangVarLike<'_>;
    fn egg_free_vars(exp: &[Self]) -> impl Iterator<Item = Var>;

    /// The highest [egg::Var] appearing in `exp`
    fn highest_egg_var(exp: &[Self]) -> uv {
        Self::egg_free_vars(exp)
            .filter_map(|v| v.as_u32())
            .max()
            .unwrap_or(0)
    }
}

impl AsLangVar for Lang {
    fn as_lang_var(&self) -> LangVarLike<'_> {
        let Lang { head, args } = self;
        LangVarLike::App { head, args }
    }

    fn egg_free_vars(_: &[Self]) -> impl Iterator<Item = Var> {
        ::std::iter::empty()
    }
}

impl AsLangVar for LangVar {
    fn as_lang_var(&self) -> LangVarLike<'_> {
        match self {
            egg::ENodeOrVar::ENode(e) => e.as_lang_var(),
            egg::ENodeOrVar::Var(var) => LangVarLike::Var(var.as_u32().unwrap()),
        }
    }

    fn egg_free_vars(exp: &[Self]) -> impl Iterator<Item = Var> {
        exp.iter().filter_map(ENodeOrVar::as_var)
    }
}

impl<'a, L: AsLangVar> Formula for RecExprIter<'a, L> {
    fn destruct(self) -> Destructed<Self, IntoIter<Self>> {
        todo!()
        // dynamic_iter!(Ret; Empty:A, App:B, Quant:C);

        // let Self { exp, vars } = self;

        // match exp.last().expect("non-empty formula").as_lang_var() {
        //     LangVarLike::App { head, args } => {
        //         // commun iterator over the arguments
        //         let mut args = args.iter().map(|&i| &exp[..=usize::from(i)]);

        //         // this is a bound variable
        //         if head == &LAMBDA_O {
        //             // crash if the bound variable is not bound
        //             let var = vars.peek();
        //             Destructed {
        //                 head: HeadSk::Var(Var::from_u32(var)),
        //                 args: Ret::Empty(::std::iter::empty()),
        //             }
        //         // this the `S` operator that increments all bound variabes.
        //         // There for we drop the closest variable since it will ne
        //         // longer be reachable
        //         } else if head == &LAMBDA_S {
        //             let exp = args.next().expect("exactly one arguement to S");
        //             Self {
        //                 exp,
        //                 // if there are no variables, then poping does nothings,
        //                 // but it should remain sound
        //                 vars: vars.dequeue(),
        //             }
        //             .destruct()
        //         // this is a binder, so we create the variable and add them to
        //         // `vars`
        //         //
        //         // *NB*: in a `find such that` the last argument still has the
        //         // variables bound even though using them there is undefined
        //         } else if head.is_egg_binder() {
        //             let min_var = Self::get_min_var_ref(exp, &vars);
        //             // fetch the sort list
        //             let sorts = {
        //                 let sort_exp = args.next().expect("a list of sorts as first arg");
        //                 sort_list::try_get(Self::from(sort_exp))
        //                     .expect("a list of sorts as first arg")
        //             };
        //             assert!(!sorts.is_empty(), "should be non-empty binder");

        //             // populate the variables
        //             let mut nvars = Vec::with_capacity(sorts.len());
        //             for (i, _) in izip!(min_var.., &sorts) {
        //                 vars.enqueue(i);
        //                 nvars.push(Var::from_u32(i));
        //             }

        //             // build the binder
        //             let binder = FOBinder::try_from_function(head).expect("a binder");
        //             let binder = RecFOFormulaQuant::new(binder, nvars.into(), sorts.into());

        //             Destructed {
        //                 head: HeadSk::Quant(binder),
        //                 // we could in theory reuse `Ret::App`, but closures
        //                 // have distinct types in rust
        //                 args: Ret::Quant(args.map(move |exp| Self {
        //                     exp,
        //                     vars: vars.clone(),
        //                 })),
        //             }
        //         // regular function application
        //         } else {
        //             Destructed {
        //                 head: HeadSk::Fun(head.clone()),
        //                 args: Ret::App(args.map(move |exp| Self {
        //                     exp,
        //                     vars: vars.clone(),
        //                 })),
        //             }
        //         }
        //     }
        //     // a free variable
        //     LangVarLike::Var(v) => Destructed {
        //         head: HeadSk::Var(Var::from_u32(v)),
        //         args: Ret::Empty(::std::iter::empty()),
        //     },
        // }
    }

    fn free_vars_iter(self) -> impl Iterator<Item = Self::Var>
    where
        Self::Quant: logic_formula::Bounder<Self::Var>,
        Self::Var: Eq + Clone,
    {
        L::egg_free_vars(self.exp)
    }

    type Var = Var;

    type Fun = Function;

    type Quant = RecFOFormulaQuant<'static>;
}

impl<'a, L: Clone> LightClone for RecExprIter<'a, L> {}

// =========================================================
// ======================= casting =========================
// =========================================================
// we use `FormulaLike` as a convenience trait

impl<L: AsLangVar> FormulaLike for [L] {
    type F<'a>
        = RecExprIter<'a, L>
    where
        L: 'a;

    fn as_formula(&self) -> Self::F<'_> {
        RecExprIter::from(self)
    }
}

impl<const N: usize, L: AsLangVar> FormulaLike for [L; N] {
    type F<'a>
        = RecExprIter<'a, L>
    where
        L: 'a;

    fn as_formula(&self) -> Self::F<'_> {
        self.as_slice().as_formula()
    }
}

impl<L: AsLangVar> FormulaLike for RecExpr<L> {
    type F<'a>
        = RecExprIter<'a, L>
    where
        L: 'a;

    fn as_formula(&self) -> Self::F<'_> {
        self.deref().as_formula()
    }
}

impl<'a, L: AsLangVar> From<&'a [L]> for RecExprIter<'a, L> {
    fn from(exp: &'a [L]) -> Self {
        Self {
            exp,
            vars: VariablesHelper::new(exp),
        }
    }
}

impl<'a, L: AsLangVar> From<RecExprIter<'a, L>> for RecFOFormula {
    fn from(v: RecExprIter<'a, L>) -> Self {
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

// =========================================================
// =================== Variable Helper =====================
// =========================================================

/// invariants: empty [Queue] means free variable `0` otherwise use [Free]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct VariablesHelper {
    /// A Queue storing the bound de Bruijn variables
    ///
    /// **invariant:** the min index of a variable inside of `var` should be *higher*
    /// than the highest variable in `exp`.
    ///
    /// `vars` is ordered, so the first element is the lowest variable.
    bound: rpds::Queue<u32>,

    /// How many `S` are need to get a free variable
    free: i64,

    /// The minimum safe variable to assign a value to, [None] means that it
    /// hasn't been calculated yet
    min_free: NonZeroU32,
}

impl VariablesHelper {
    fn new<L: AsLangVar>(exp: &[L]) -> Self {
        let min_free = NonZeroU32::new(L::highest_egg_var(exp) + 1).unwrap();
        Self {
            bound: Default::default(),
            free: 0,
            min_free,
        }
    }

    fn peek_last(&self) -> u32 {
        todo!()
        // match (self.bound.peek(), u32::try_from(self.free)) {
        //     (Some(x),_) => x,
        //     (_, Ok(x)) => x + self.min_free,
        //     _ => panic!("the variable pile is empty, but the stacks says otherwise")
        // }

        // match self {
        //     VariablesHelper::Bound(queue) => queue.peek().copied().unwrap_or_default(),
        //     VariablesHelper::Free { depth } => (*depth).into(),
        // }
    }

    fn pop(&self) -> Self {
        todo!()
        // match self {
        //     Self::Bound(queue) => match queue.dequeue() {
        //         Some(x) => Self::Bound(x),
        //         None => Self::Free {
        //             depth: NonZeroU32::new(1).unwrap(),
        //         },
        //     },
        //     Self::Free { depth } => Self::Free {
        //         depth: depth.checked_add(1).unwrap(),
        //     },
        // }
    }

    fn bind(&self, i: u32) -> Self {
        todo!()
        // match self {
        //     Self::Bound(q) => Self::Bound(q.enqueue(i)),
        //     _ => Self::Bound(rpds::Queue::default().enqueue(i)),
        // }
    }
}
