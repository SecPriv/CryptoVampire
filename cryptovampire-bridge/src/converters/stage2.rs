
use std::borrow::Cow;
use crate::json::{self, SquirrelDump};

use super::{stage0::inline_lets, stage1::convert_json_to_1, Result};

use cryptovampire_lib::formula::{variable::uvar, BaseFormula};
use hashbrown::HashSet;
use itertools::Itertools;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fun2<'a> {
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
pub struct SVariable(uvar);

pub type TF2<'a> = BaseFormula<SQuant, Fun2<'a>, SVariable>;
pub type SquirrelDump2<'a> = SquirrelDump<'a, TF2<'a>, SVariable>;

mod varset {
  use cryptovampire_lib::formula::variable::from_usize;
  use utils::implvec;

  use crate::json;

  use super::SVariable;

  pub struct VarSet<'a>(Vec<json::Variable<'a>>);

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

      pub fn into_svarlist(self) -> Vec<SVariable> {
          (0..self.0.len()).map(from_usize).map(SVariable).collect()
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

pub use varset::VarSet;

use super::{stage1::{Fun1, TF1}, ConversiontError, SQuant};

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
      } => Err(ConversiontError::TooMuchHighOrder),
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

fn from_json_to_2<'a>(free_vars: &mut VarSet<'a>, f: json::Term<'a>) -> Result<TF2<'a>> {
  let f = inline_lets(&mut Default::default(), f);
  let f = convert_json_to_1(f)?;
  convert_1_to_2(free_vars, f)
}



mod sq_to_2 {
  use itertools::Itertools;

  use crate::{
      json::{self, action::Action, Operator, SquirrelDump},
  };

  use super::{SVariable, TF2};
  use super::{from_json_to_2, Result, SquirrelDump2};

  mod action {
      use super::super::Result;
      use cryptovampire_lib::formula::variable::from_usize;
      use itertools::Itertools;

      use crate::{
          converters::stage2::{from_json_to_2, SVariable, VarSet, TF2}, json::{self, action}
      };

      /// Convert the [json::Action::action] field. That is a squirrel `action_v` type.
      ///
      /// I'm assuming the variables are not linked in anyway to the rest of
      /// the declaration. Thus, I am just making sure that each variable is
      /// unique and that when two json::Variables are the same then the SVariable
      /// are also the same */
      pub fn convert_shape<'a>(
          a: action::AT<Vec<json::Variable<'a>>>,
      ) -> action::AT<Vec<SVariable>> {
          let mut aux2 = {
              let mut tmp = vec![];
              move |x| {
                  tmp.iter().position(|y| &x == y).unwrap_or_else(|| {
                      let n = tmp.len();
                      tmp.push(x);
                      n
                  })
              }
          };
          a.into_iter()
              .map(
                  |action::Item {
                       par_choice: (ip, vp),
                       sum_choice: (is, vs),
                   }| {
                      let [vp, vs] = [vp, vs].map(|v| {
                          v.into_iter()
                              .map(&mut aux2)
                              .map(from_usize)
                              .map(SVariable)
                              .collect()
                      });
                      action::Item {
                          par_choice: (ip, vp),
                          sum_choice: (is, vs),
                      }
                  },
              )
              .collect()
      }

      pub fn convert_condition<'a>(
          free_vars: &mut VarSet<'a>,
          action::Condition { vars, term }: action::Condition<json::Term<'a>, json::Variable<'a>>,
      ) -> Result<action::Condition<TF2<'a>, SVariable>> {
          free_vars.with_new_vars(vars, |varset, vars| {
              let term = from_json_to_2(varset, term)?;
              Ok(action::Condition { vars, term })
          })
      }

      pub fn convert_output<'a>(
          free_vars: &mut VarSet<'a>,
          action::Ouptut { channel, term }: action::Ouptut<'a, json::Term<'a>>,
      ) -> Result<action::Ouptut<'a, TF2<'a>>> {
          Ok(action::Ouptut {
              channel,
              term: from_json_to_2(free_vars, term)?,
          })
      }

      pub fn convert_update<'a>(
          free_vars: &mut VarSet<'a>,
          action::Update { symb, args, body }: action::Update<'a, json::Term<'a>>,
      ) -> Result<action::Update<'a, TF2<'a>>> {
          let args = args
              .into_iter()
              .map(|f| from_json_to_2(free_vars, f))
              .try_collect()?;
          let body = from_json_to_2(free_vars, body)?;
          Ok(action::Update { symb, args, body })
      }
  }

  fn convert_action<'a>(
      Action {
          name,
          action,
          input,
          indices,
          condition,
          updates,
          output,
          globals,
      }: Action<'a>,
  ) -> Result<Action<'a, TF2<'a>, SVariable>> {
      let mut free_vars = indices.into_iter().collect();

      let action = action::convert_shape(action);
      let condition = action::convert_condition(&mut free_vars, condition)?;
      let updates = updates
          .into_iter()
          .map(|u| action::convert_update(&mut free_vars, u))
          .try_collect()?;
      let output = action::convert_output(&mut free_vars, output)?;
      let indices = free_vars.into_svarlist();
      Ok(Action {
          name,
          action,
          input,
          indices,
          condition,
          updates,
          output,
          globals,
      })
  }

  mod operator {
      use crate::{
          converters::stage2::{from_json_to_2, Result, SVariable, TF2},
          json::{
              self,
              operator::{Concrete, Def},
          },
      };

      pub fn convert_concrete<'a>(
          Concrete {
              name,
              type_variables,
              args,
              out_type,
              body,
          }: Concrete<'a, json::Term<'a>, json::Variable<'a>, json::Type<'a>>,
      ) -> Result<Concrete<'a, TF2<'a>, SVariable, json::Type<'a>>> {
          let mut free_vars = args.into_iter().collect();
          let body = from_json_to_2(&mut free_vars, body)?;
          let args = free_vars.into_svarlist();
          Ok(Concrete {
              name,
              type_variables,
              args,
              out_type,
              body,
          })
      }
      pub fn convert_def<'a>(
          d: Def<'a, json::Term<'a>, json::Variable<'a>, json::Type<'a>>,
      ) -> Result<Def<'a, TF2<'a>, SVariable, json::Type<'a>>> {
          Ok(match d {
              Def::Abstract {
                  abstract_def,
                  associated_fun,
              } => Def::Abstract {
                  abstract_def,
                  associated_fun,
              },
              Def::Concrete(c) => Def::Concrete(convert_concrete(c)?),
          })
      }
  }

  fn convert_operator<'a>(
      json::Content {
          symb,
          data: json::operator::Data { sort, def },
      }: Operator<'a>,
  ) -> Result<Operator<'a, TF2<'a>, SVariable>> {
      let def = operator::convert_def(def)?;
      Ok(json::Content {
          symb,
          data: json::operator::Data { sort, def },
      })
  }

  pub fn from_sq_dump_to_2<'a>(dump: SquirrelDump<'a>) -> Result<SquirrelDump2<'a>> {
      let SquirrelDump {
          query,
          hypotheses,
          variables,
          actions,
          names,
          operators,
          macros,
          types,
      } = dump;

      let mut free_vars = variables.into_iter().collect();
      let query = Box::new(from_json_to_2(&mut free_vars, *query)?);
      let hypotheses = hypotheses
          .into_iter()
          .map(|f| from_json_to_2(&mut free_vars, f))
          .try_collect()?;
      let actions = actions.into_iter().map(convert_action).try_collect()?;
      let operators = operators.into_iter().map(convert_operator).try_collect()?;

      let variables = free_vars.into_svarlist();
      Ok(SquirrelDump2 {
          query,
          hypotheses,
          variables,
          actions,
          names,
          operators,
          macros,
          types,
      })
  }
}