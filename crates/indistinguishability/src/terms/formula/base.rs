use itertools::Either;
use logic_formula::{AsFormula, Destructed, HeadSk};
use rustc_hash::FxHashMap;
use utils::{dynamic_iter, match_eq};

use super::{FOBinder, Formula, RecFOFormulaQuant};
use crate::terms::formula::RecFOFormulaQuantRef;
use crate::terms::{AND, FALSE, Function, IMPLIES, NOT, OR, Sort, TRUE, Variable};

impl Formula {
    pub fn as_var(&self) -> Option<&Variable> {
        match self {
            Self::Var(v) => Some(v),
            _ => None,
        }
    }

    /// Tries to evaluate an expression, return [None] if it can't
    pub fn try_evaluate(&self) -> Option<bool> {
        match self {
            Formula::App { head, args } => {
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
            Formula::Quantifier {
                head: FOBinder::Exists,
                arg,
                ..
            }
            | Formula::Quantifier {
                head: FOBinder::Forall,
                arg,
                ..
            } => arg[0].try_evaluate(),
            _ => None,
        }
    }

    /// Returns the [Sort] of `self`, [None] if it is a variable
    ///
    /// **NB**:
    /// - doesn't typechecks
    pub fn try_get_sort(&self) -> Option<Sort> {
        match self {
            Formula::Quantifier {
                head: FOBinder::FindSuchThat,
                ..
            } => Some(Sort::Bitstring),
            Formula::Quantifier { .. } => Some(Sort::Bool),
            Formula::App { head, .. } => Some(head.signature.output),
            Formula::Var(_) => None,
        }
    }

    /// Checks that the terms has the given sort.
    ///
    /// This doesn't typechecks
    pub fn has_sort(&self, sort: Sort) -> bool {
        match self.try_get_sort() {
            Some(Sort::Any) | None => true,
            Some(x) => x == sort || sort == Sort::Any,
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
impl Formula {
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

fn find<'a>(
    var: &'a Variable,
    subst: &'a FxHashMap<Variable, Formula>,
    seen: &mut Vec<Variable>,
) -> Result<Either<&'a Formula, &'a Variable>, &'a Variable> {
    match subst.get(var) {
        Some(Formula::Var(nv)) if seen.contains(nv) => Err(var),
        Some(Formula::Var(var)) => {
            seen.push(var.clone());
            find(var, subst, seen)
        }
        Some(x) => Ok(Either::Left(x)),
        _ => Ok(Either::Right(var)),
    }
}

impl Default for Formula {
    fn default() -> Self {
        Self::App {
            head: TRUE.clone(),
            args: Default::default(),
        }
    }
}
impl AsFormula for Formula {
    type Var = Variable;

    type Fun = Function;

    type Quant = RecFOFormulaQuant;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            Formula::Quantifier { head, vars, arg } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuant::new(head, vars.as_owned())),
                args: MIter::One(arg.as_owned().into_iter()),
            },
            Formula::App { head, args } => Destructed {
                head: HeadSk::Fun(head.clone()),
                args: MIter::Many(args.as_owned().into_iter()),
            },
            Formula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl<'b> AsFormula for &'b Formula {
    type Var = &'b Variable;

    type Fun = &'b Function;

    type Quant = RecFOFormulaQuantRef<'b>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            Formula::Quantifier { head, vars, arg } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuantRef::new(*head, vars.as_ref())),
                args: MIter::One(arg.iter()),
            },
            Formula::App { head, args } => Destructed {
                head: HeadSk::Fun(head),
                args: MIter::Many(args.iter()),
            },
            Formula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}
