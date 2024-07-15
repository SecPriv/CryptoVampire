use std::borrow::Cow;

use cryptovampire_lib::formula::{sort::inner::Other, variable::uvar, BaseFormula};
use hashbrown::HashMap;
use itertools::Itertools;
use thiserror::Error;

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

#[derive(Debug, Clone)]
enum Fun2<'a> {
    Name(Cow<'a, str>),
    Macro(Cow<'a, str>),
    Step(Cow<'a, str>),
    Fun(Cow<'a, str>),
    Tuple,
    ProjL,
    ProjR,
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
fn convert<'a>(t: json::Term<'a>) -> Result<TF1<'a>> {
    use json::Term::*;
    match t {
        App { f, args } => {
            let args = args.into_iter().map(|x| convert(x)).try_collect()?;
            match *f {
                App { .. } => Ok(TF1::App {
                    head: Fun1::Term(Box::new(convert(*f)?)),
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
            let args = args.into_iter().map(|x| convert(x)).try_collect()?;
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
                .map(|x| convert(x))
                .try_collect()?;
            Ok(TF1::App {
                head: Fun1::Macro(symb),
                args,
            })
        }
        Action { symb, args } => {
            let args = args.into_iter().map(|x| convert(x)).try_collect()?;
            Ok(TF1::App {
                head: Fun1::Step(symb),
                args,
            })
        }
        Var { var } => Ok(TF1::Var(var)),
        Tuple { elements } => {
            let n = elements.len() as utuple;
            let args = elements.into_iter().map(|x| convert(x)).try_collect()?;
            Ok(TF1::App {
                head: Fun1::Tuple(n),
                args,
            })
        }
        Proj { id, body } => {
            let args = [*body].into_iter().map(|x| convert(x)).try_collect()?;
            Ok(TF1::App {
                head: Fun1::Proj(id),
                args,
            })
        }
        Diff { terms } => {
            let args = terms
                .into_iter()
                .sorted_by(|a, b| Ord::cmp(&a.proj, &b.proj))
                .map(|x| convert(x.term))
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
                .map(|x| convert(x))
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
            let args = [*body].into_iter().map(|x| convert(x)).try_collect()?;
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
        _ => unreachable!("unsupported `Term` and `Diff` variant, or unsuported projection"),
    }
}
