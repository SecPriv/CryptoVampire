use std::borrow::Cow;

use cryptovampire_lib::formula::{sort::inner::Other, variable::uvar, BaseFormula};
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use thiserror::Error;
use utils::implvec;

use crate::json;

#[derive(Debug, Error)]
enum ConversiontError {
    #[error("unsupported binder")]
    UnsupportedBinder,
    #[error("unsuported macro: frame and global macros are not supported")]
    UnsupportedMacro,
    #[error("The fun constructor is misplaced")]
    MisplacedFun,
    #[error("Unsupported head. (usually because an apllied Name or Macros was put as a head")]
    UnssupportedHead,
    #[error("A binder has parameters that aren't variables")]
    NonVariableInQuantifier,
    #[error("The only supported binders are forall, exists and fins such that.")]
    UnssupportedQuantifier,
    #[error(
        "The problem makes use of high order functions which cannot be simplified by CryptoVampire"
    )]
    HighOrder,
    #[error("Diffs don't inlude the same number of protocol each time")]
    InconsistenDiff,
    #[error("Wrong number of arguments, expected {expected:}, got {got:}")]
    WrongNumberOfArguements { expected: usize, got: usize },
    #[error("A variable is not assigned")]
    UnassignedVariable,
    #[error("Other converstion error: {0}")]
    Other(Box<str>),
}

#[allow(non_camel_case_types)]
type utuple = u8;

#[derive(Debug, Clone)]
enum Fun1<'a> {
    Term(Box<TF1<'a>>),
    Name(Cow<'a, str>),
    Macro(Cow<'a, str>),
    Step(Cow<'a, str>),
    Fun(Cow<'a, str>),
    Tuple(u8),
    Proj(u8),
    Diff,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Fun2<'a> {
    Name(Cow<'a, str>),
    Macro(Cow<'a, str>),
    Step(Cow<'a, str>),
    Fun(Cow<'a, str>),
    Tuple,
    ProjL,
    ProjR,
    Diff,
    Empty,
}

#[derive(Debug, Clone)]
enum SQuant {
    Forall,
    Exists,
    FindSuchThat,
}

#[derive(Debug, Clone)]
pub struct SVariable(uvar);

type TF1<'a> = BaseFormula<SQuant, Fun1<'a>, json::Variable<'a>>;
type TF2<'a> = BaseFormula<SQuant, Fun2<'a>, SVariable>;

type Result<A> = std::result::Result<A, ConversiontError>;

fn try_into_vars<'a>(t: json::Term<'a>) -> Option<json::Variable<'a>> {
    match t {
        json::Term::Var { var } => Some(var),
        _ => None,
    }
}

/// Convert a squirrel [json::Term] is a preliminary [TF1].
///
/// There most be:
/// * no lets
/// * only terms supported by cv.
fn convert_json_to_1<'a>(t: json::Term<'a>) -> Result<TF1<'a>> {
    use json::Term::*;
    match t {
        App { f, args } => {
            let args = args
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            match *f {
                App { .. } => Ok(TF1::App {
                    head: Fun1::Term(Box::new(convert_json_to_1(*f)?)),
                    args,
                }),
                Fun { symb } => Ok(TF1::App {
                    head: Fun1::Fun(symb),
                    args,
                }),
                _ => Err(ConversiontError::UnssupportedHead),
            }
        }
        Name { symb, args } => {
            let args = args
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Name(symb),
                args,
            })
        }
        Macro {
            symb,
            args,
            timestamp,
        } => {
            let args = args
                .into_iter()
                .chain([*timestamp])
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Macro(symb),
                args,
            })
        }
        Action { symb, args } => {
            let args = args
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Step(symb),
                args,
            })
        }
        Var { var } => Ok(TF1::Var(var)),
        Tuple { elements } => {
            let n = elements.len() as utuple;
            let args = elements
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Tuple(n),
                args,
            })
        }
        Proj { id, body } => {
            let args = [*body]
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Proj(id),
                args,
            })
        }
        Diff { terms } => {
            let args = terms
                .into_iter()
                .sorted_by(|a, b| Ord::cmp(&a.proj, &b.proj))
                .map(|x| convert_json_to_1(x.term))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Diff,
                args,
            })
        }
        Find {
            vars,
            condition,
            success,
            faillure,
        } => {
            let vars = vars
                .into_iter()
                .map(|v| try_into_vars(v).ok_or(ConversiontError::NonVariableInQuantifier))
                .try_collect()?;
            let args = [*condition, *success, *faillure]
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::Binder {
                head: SQuant::FindSuchThat,
                vars,
                args,
            })
        }
        Quant {
            quantificator,
            vars,
            body,
        } => {
            let head = match quantificator {
                json::Quant::ForAll => SQuant::Forall,
                json::Quant::Exists => SQuant::Exists,
                _ => return Err(ConversiontError::UnssupportedQuantifier),
            };
            let vars = vars
                .into_iter()
                .map(|v| try_into_vars(v).ok_or(ConversiontError::NonVariableInQuantifier))
                .try_collect()?;
            let args = [*body]
                .into_iter()
                .map(|x| convert_json_to_1(x))
                .try_collect()?;
            Ok(TF1::Binder { head, vars, args })
        }
        Let { .. } => Err(ConversiontError::Other("no lets at this point".into())),
        Fun { .. } => {
            // this means it is a fun by itself. It should have been caught by the `App` case before
            Err(ConversiontError::MisplacedFun)
        }
    }
}

fn inline_lets<'a>(
    subst: &mut HashMap<json::Term<'a>, json::Term<'a>>,
    t: json::Term<'a>,
) -> json::Term<'a> {
    if let Some(x) = subst.get(&t) {
        x.clone()
    } else {
        use json::Term::*;
        match t {
            App { f, args } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                App { f, args }
            }
            Name { symb, args } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                Name { symb, args }
            }
            Macro {
                symb,
                args,
                timestamp,
            } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                let timestamp = Box::new(inline_lets(subst, *timestamp));
                Macro {
                    symb,
                    args,
                    timestamp,
                }
            }
            Action { symb, args } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                Action { symb, args }
            }
            Let { var, decl, body } => {
                let old = subst.get(&*var).cloned();
                let decl = inline_lets(subst, *decl);
                subst.insert((*var).clone(), decl);
                let body = inline_lets(subst, *body);
                if let Some(old) = old {
                    subst.insert(*var, old);
                }
                body
            }
            Tuple { elements } => {
                let elements = elements
                    .into_iter()
                    .map(|t| inline_lets(subst, t))
                    .collect();
                Tuple { elements }
            }
            Proj { id, body } => Proj {
                id,
                body: Box::new(inline_lets(subst, *body)),
            },
            Diff { terms } => {
                let terms = terms
                    .into_iter()
                    .map(|json::Diff { proj, term }| json::Diff {
                        proj,
                        term: inline_lets(subst, term),
                    })
                    .collect();
                Diff { terms }
            }
            Find {
                vars,
                condition,
                success,
                faillure,
            } => {
                let [condition, success, faillure] = [condition, success, faillure]
                    .map(|t| inline_lets(subst, *t))
                    .map(Box::new);
                let vars = vars.into_iter().map(|t| inline_lets(subst, t)).collect();
                Find {
                    vars,
                    condition,
                    success,
                    faillure,
                }
            }
            Quant {
                quantificator,
                vars,
                body,
            } => {
                let [body] = [body].map(|t| inline_lets(subst, *t)).map(Box::new);
                let vars = vars.into_iter().map(|t| inline_lets(subst, t)).collect();
                Quant {
                    quantificator,
                    vars,
                    body,
                }
            }
            Var { .. } | Fun { .. } => t,
        }
    }
}

/// converts from [Fun1] to [Fun2] and panics if impossible
///
/// ### Invariants:
/// * no [Fun1::Term] or [Fun1::Diff] variants
/// * only `Fun1::Tuple(2)`, `Fun1::Proj(0)` and `Fun1::Proj(1)` when it comes to projections
fn convert_fun<'a>(f1: Fun1<'a>) -> Fun2<'a> {
    match f1 {
        Fun1::Name(n) => Fun2::Name(n),
        Fun1::Macro(n) => Fun2::Macro(n),
        Fun1::Step(n) => Fun2::Step(n),
        Fun1::Fun(n) => Fun2::Fun(n),
        Fun1::Tuple(2) => Fun2::Tuple,
        Fun1::Proj(0) => Fun2::ProjL,
        Fun1::Proj(1) => Fun2::ProjR,
        Fun1::Diff => Fun2::Diff,
        _ => unreachable!("unsupported `Term` variant, or unsuported projection"),
    }
}

mod varset {
    use cryptovampire_lib::formula::variable::from_usize;
    use utils::implvec;

    use crate::json;

    use super::SVariable;

    pub(crate) struct VarSet<'a>(Vec<json::Variable<'a>>);

    impl<'a> VarSet<'a> {
        pub fn get_var(&mut self, var: &json::Variable<'a>) -> Option<SVariable> {
            self.0
                .iter()
                .rev()
                .position(|x| x == var)
                .map(from_usize)
                .map(SVariable)
        }

        pub fn with_new_vars<F, U>(&mut self, vars: implvec!(json::Variable<'a>), f: F) -> U
        where
            for<'b> F: FnOnce(&'b mut Self, Vec<SVariable>) -> U,
        {
            let n = self.0.len();
            self.0.extend(vars);
            let nvars = (n..self.0.len()).map(from_usize).map(SVariable).collect();
            let ret = f(self, nvars); // call the function
            self.0.truncate(n);
            ret
        }
    }

    impl<'a> IntoIterator for VarSet<'a> {
        type Item = <Vec<json::Variable<'a>> as IntoIterator>::Item;

        type IntoIter = <Vec<json::Variable<'a>> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl<'a> FromIterator<json::Variable<'a>> for VarSet<'a> {
        fn from_iter<T: IntoIterator<Item = json::Variable<'a>>>(iter: T) -> Self {
            Self(Vec::from_iter(iter))
        }
    }
}

fn convert_1_to_2<'a>(varset: &mut varset::VarSet<'a>, f: TF1<'a>) -> Result<TF2<'a>> {
    match f {
        TF1::Binder { head, vars, args } => varset.with_new_vars(vars, |varset, vars| {
            let args = args
                .into_iter()
                .map(|x| convert_1_to_2(varset, x))
                .try_collect()?;
            Ok(TF2::Binder { head, vars, args })
        }),
        TF1::App {
            head: Fun1::Term(_),
            args: _,
        } => Err(ConversiontError::HighOrder),
        TF1::App {
            // fold tuples
            head: Fun1::Tuple(i),
            args,
        } => {
            if (i as usize) != args.len() {
                // u8 < usize, so no problem
                return Err(ConversiontError::WrongNumberOfArguements {
                    expected: i as usize,
                    got: args.len(),
                });
            }
            let mut args: Vec<_> = args
                .into_iter()
                .map(|x| convert_1_to_2(varset, x))
                .try_collect()?;
            Ok(match i {
                0 => TF2::App {
                    head: Fun2::Empty,
                    args: vec![],
                },
                1 => {
                    let [arg]: [_; 1] = args.try_into().unwrap();
                    arg
                }
                _ => {
                    let right = args.pop().unwrap(); // can't fail
                    let left = args.pop().unwrap(); //can't fail
                    let init = TF2::App {
                        head: Fun2::Tuple,
                        args: vec![left, right],
                    };
                    args.into_iter().fold(init, |tail, head| TF2::App {
                        head: Fun2::Tuple,
                        args: vec![head, tail],
                    })
                }
            })
        }
        TF1::App {
            head: Fun1::Proj(i),
            args,
        } => {
            let [arg] = <[_; 1] as TryFrom<Vec<_>>>::try_from(args)
                .map_err(|args| ConversiontError::WrongNumberOfArguements {
                    expected: 1,
                    got: args.len(),
                })?
                .map(|x| convert_1_to_2(varset, x));
            fn aux<'a>(n: u8, arg: TF2<'a>) -> TF2<'a> {
                match n {
                    0 => TF2::App {
                        head: Fun2::ProjL,
                        args: vec![arg],
                    },
                    1 => TF2::App {
                        head: Fun2::ProjR,
                        args: vec![arg],
                    },
                    _ => TF2::App {
                        head: Fun2::ProjR,
                        args: vec![aux(n - 1, arg)],
                    },
                }
            }
            Ok(aux(i, arg?))
        }
        TF1::App { head, args } => {
            let head = convert_fun(head);
            let args = args
                .into_iter()
                .map(|x| convert_1_to_2(varset, x))
                .try_collect()?;
            Ok(TF2::App { head, args })
        }
        TF1::Var(v) => varset
            .get_var(&v)
            .map(TF2::Var)
            .ok_or(ConversiontError::UnassignedVariable),
    }
}

fn from_json_to_2<'a>(
    free_vars: implvec!(json::Variable<'a>),
    f: json::Term<'a>,
) -> Result<TF2<'a>> {
    let mut vars = free_vars.into_iter().collect();
    let f = inline_lets(&mut Default::default(), f);
    let f = convert_json_to_1(f)?;
    convert_1_to_2(&mut vars, f)
}

fn find_used_symbols<'a>(symbs: &mut HashSet<Fun2<'a>>, f: &TF2<'a>) {
    match f {
        BaseFormula::Binder { args, .. } => args.iter().for_each(|f| find_used_symbols(symbs, f)),
        BaseFormula::App { head, args } => {
            symbs.insert(head.clone());
            args.iter().for_each(|f| find_used_symbols(symbs, f))
        }
        BaseFormula::Var(_) => (),
    }
}
