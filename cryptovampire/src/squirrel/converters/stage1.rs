use std::borrow::Cow;

use cryptovampire_lib::formula::BaseFormula;
use itertools::Itertools;

use super::super::{converters::{utuple, ConversiontError}, json};

use super::{SQuant, Result};



#[derive(Debug, Clone)]
pub enum Fun1<'a> {
    Term(Box<TF1<'a>>),
    Name(Cow<'a, str>),
    Macro(Cow<'a, str>),
    Step(Cow<'a, str>),
    Fun(Cow<'a, str>),
    Tuple(u8),
    Proj(u8),
    Diff,
}
pub type TF1<'a> = BaseFormula<SQuant, Fun1<'a>, json::Variable<'a>>;

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
pub fn convert_json_to_1<'a>(t: json::Term<'a>) -> Result<TF1<'a>> {
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
                _ => return Err(ConversiontError::UnsupportedQuantifier),
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
