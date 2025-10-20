use std::borrow::Cow;

use logic_formula::{Destructed, Formula, HeadSk};
use utils::dynamic_iter;

use crate::terms::{FOBinder, Function, Variable};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum VExprHead {
    Var(Variable),
    Quantifier {
        head: FOBinder,
        vars: Vec<Variable>,
        /// The offset from the current position to the index of the head arguments
        args: Vec<usize>,
    },
    App {
        head: Function,
        /// The offset from the current position to the index of the head arguments
        args: Vec<usize>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VExprQuant<'a> {
    head: FOBinder,
    vars: Cow<'a, [Variable]>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VExpr(pub Vec<VExprHead>);
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct VExprRef<'a>(pub &'a [VExprHead]);

impl<'a> Formula for VExprRef<'a> {
    type Var = &'a Variable;

    type Fun = &'a Function;

    type Quant = VExprQuant<'a>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; Many:B, None:C);
        let head = self.as_slice().first().expect("destructing empty formula");
        match head {
            VExprHead::Var(variable) => Destructed {
                head: HeadSk::Var(variable),
                args: MIter::None(std::iter::empty()),
            },
            VExprHead::Quantifier { head, vars, args } => Destructed {
                head: HeadSk::Quant(VExprQuant {
                    head: *head,
                    vars: Cow::Borrowed(&vars),
                }),
                args: MIter::Many(mk_args_iter(self, &args)),
            },
            VExprHead::App { head, args } => Destructed {
                head: HeadSk::Fun(head),
                args: MIter::Many(mk_args_iter(self, &args)),
            },
        }
    }
}

impl VExpr {
  #[inline]
  pub fn as_ref(&self) -> VExprRef<'_> {
    VExprRef(&self.0)
  }
}

impl<'a> VExprRef<'a> {
    #[inline]
    pub fn as_slice(&self) -> &'a [VExprHead] {
        self.0
    }
}

impl 

fn mk_args_iter<'a>(f: VExprRef<'a>, args: &'a [usize]) -> impl Iterator<Item = VExprRef<'a>> {
    args.iter().map(move |&i| VExprRef(&f.as_slice()[i..]))
}
