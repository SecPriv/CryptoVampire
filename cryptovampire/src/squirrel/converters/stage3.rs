use std::borrow::Cow;

use super::Result;
use anyhow::Context;
use cryptovampire_lib::{
    container::{utils::NameFinder, ScopedContainer},
    formula::{
        function::{inner::name::Name, Function},
        sort::{
            builtins::{BOOL, CONDITION, MESSAGE, NAME, STEP},
            Sort,
        },
        variable::uvar,
        BaseFormula,
    },
};
use hashbrown::{HashMap, HashSet};
use itertools::{chain, Itertools};
use utils::{implvec, string_ref::StrRef};

use crate::{
    err_at,
    parser::{ast, InputError, Location, MResult},
    squirrel::{
        converters::ConversiontError,
        json::{
            self,
            action::Update,
            operator::{Concrete, Def},
            Action, Content, FunctionType,
        },
    },
};

use super::stage2::{Fun2, SVariable, SquirrelDump2, TF2};

fn try_into_array<A, B, const N: usize>(a: Vec<A>) -> MResult<[B; N]>
where
    A: TryInto<B, Error = InputError>,
{
    let tmp: std::result::Result<Vec<B>, InputError> =
        a.into_iter().map(|x| x.try_into()).collect();
    Ok(tmp?
        .try_into()
        .map_err(|_| err_at!(&Location::none(), "wrong number of arguments"))?)
}

impl<'a> TryInto<ast::Term<'static>> for TF2<'a> {
    type Error = InputError;
    fn try_into(self) -> MResult<ast::Term<'static>> {
        let span = Location::none();
        let inner = match self {
            BaseFormula::Binder { head, vars, args } => {
                let vars = vars.into_iter().map(|x| x.try_into()).try_collect()?;
                match head {
                    super::SQuant::Forall | super::SQuant::Exists => {
                        let [content]: [_; 1] = try_into_array(args)?;
                        let kind = match head {
                            super::SQuant::Exists => ast::QuantifierKind::Exists,
                            super::SQuant::Forall => ast::QuantifierKind::Forall,
                            _ => unreachable!(),
                        };
                        ast::InnerTerm::Quant(Box::new(ast::Quantifier {
                            span,
                            vars,
                            kind,
                            content,
                        }))
                    }
                    super::SQuant::FindSuchThat => {
                        let [condition, left, right]: [_; 3] = try_into_array(args)?;
                        ast::InnerTerm::Fndst(Box::new(ast::FindSuchThat {
                            span,
                            vars,
                            condition,
                            left,
                            right,
                        }))
                    }
                }
            }
            BaseFormula::App { head, args } => todo!(),
            BaseFormula::Var(v) => {
                ast::InnerTerm::Application(ast::Application::ConstVar { span, content: v.id.name })
            },
        };

        Ok(ast::Term { span, inner })
    }
}

#[derive(Debug)]
struct SquirrelData<'a> {
    pub operators: HashMap<String, json::operator::Data<'a, TF2<'a>, SVariable, json::Type<'a>>>,
    pub types: HashMap<String, json::mtype::SortData>,
    pub actions: HashMap<String, Action<'a, TF2<'a>, SVariable>>,
    pub names: HashMap<String, FunctionType<'a, json::Type<'a>>>,
    pub macros: HashMap<String, json::mmacro::Data<json::Type<'a>>>,
}

// fn gather_sq_data<'a>(
//     SquirrelDump2 {
//         // query,
//         // hypotheses,
//         actions,
//         operators,
//         // variables,
//         names,
//         // macros,
//         types,
//         ..
//     }: SquirrelDump2<'a>,
// ) -> SquirrelData<'a> {
//     let actions = actions
//         .into_iter()
//         .map(|a| (a.name.as_ref().into(), a))
//         .collect();
//     let types = types
//         .into_iter()
//         .map(|Content { data, symb }| (symb.into(), data))
//         .collect();
//     let operators = operators
//         .into_iter()
//         .map(|Content { symb, data }| (symb.into(), data))
//         .collect();
//     let names = names
//         .into_iter()
//         .map(|Content { symb, data }| (symb.into(), data))
//         .collect();
//     todo!()
//     // SquirrelData {
//     //     operators,
//     //     types,
//     //     actions,
//     //     names,
//     // }
// }

#[derive(Debug)]
struct AnlysedSq<'a> {
    fun_set: HashSet<Fun2<'a>>,
    diff_width: usize,
}

/// Gather some info, notatbly:
///
/// * which symbols are used. This way if weird symbols are declared but not used, we can ignore them
/// * make sure the diff make sense and gets the width
fn analyse<'a>(
    SquirrelDump2 {
        query,
        hypotheses,
        actions,
        operators,
        ..
    }: &SquirrelDump2<'a>,
) -> Result<AnlysedSq<'a>> {
    fn find_used_symbols_in_formula<'a>(ansq: &mut AnlysedSq<'a>, f: &TF2<'a>) -> Result<()> {
        let symbs = &mut ansq.fun_set;
        match f {
            BaseFormula::Binder { args, .. } => args
                .iter()
                .try_for_each(|f| find_used_symbols_in_formula(ansq, f)),
            BaseFormula::App { head, args } => {
                match head {
                    Fun2::Diff => {
                        let width = args.len();
                        if width == 0 || (ansq.diff_width != 0 && ansq.diff_width != width) {
                            return Err(ConversiontError::InvalidDiff);
                        } else {
                            ansq.diff_width = width
                        }
                    }
                    _ => (),
                }
                symbs.insert(head.clone());
                args.iter()
                    .try_for_each(|f| find_used_symbols_in_formula(ansq, f))
            }
            BaseFormula::Var(_) => Ok(()),
        }
    }
    let mut ansq = AnlysedSq {
        fun_set: HashSet::default(),
        diff_width: 0,
    };

    let actions_iter = actions.iter().flat_map(
        |Action {
             condition,
             updates,
             output,
             ..
         }| {
            let updates_iter = updates
                .iter()
                .flat_map(|Update { args, body, .. }| chain!([body], args));
            chain!([&condition.term, &output.term], updates_iter)
        },
    );

    let operator_iter = operators.iter().filter_map(|o| match &o.data.def {
        Def::Concrete(Concrete { body, .. }) => Some(body),
        _ => None,
    });

    chain!([query.as_ref()], hypotheses, actions_iter, operator_iter)
        .try_for_each(|f| find_used_symbols_in_formula(&mut ansq, f))?;

    Ok(ansq)
}

struct SortFinder<'bump> {
    index: Sort<'bump>,
}

impl<'bump> SortFinder<'bump> {
    pub fn new(container: &'bump ScopedContainer<'bump>) -> Self {
        let idxname = container.find_free_name("idx");
        let index = Sort::new_index(container, idxname.into());
        Self { index }
        // tys.into_iter()
        //     .map(|(name, t)| {
        //         if !t.0.iter().any(|x| x.can_be_index()) {
        //             Ok((MESSAGE.name(), MESSAGE.clone()))
        //         } else {
        //             let s = Sort::new_index(container, name.into());
        //             Ok((s.name(), s))
        //         }
        //     })
        //     .try_collect()
        //     .map(Self)
    }

    pub fn get_sort<'a>(&self, s: &json::Type<'a>) -> Option<Sort<'bump>> {
        match s {
            json::Type::Message => Some(MESSAGE.clone()),
            json::Type::Boolean => Some(CONDITION.clone()),
            json::Type::Index => Some(self.index),
            json::Type::Timestamp => Some(STEP.clone()),
            json::Type::TBase(_) => Some(MESSAGE.clone()), // no support for types
            json::Type::TVar { ident } | json::Type::TUnivar { ident } => unimplemented!(),
            json::Type::Tuple { elements } => Some(MESSAGE.clone()),
            json::Type::Fun { t_in, out } => unimplemented!(),
        }
    }
}

#[derive(Debug)]
enum Apply<'bump, 'a> {
    Replace { args: Vec<uvar>, to: TF2<'a> },
    Name(Function<'bump>, Sort<'bump>),
}

fn declare_funs<'bump, 'a, 'b>(
    container: &'bump ScopedContainer<'bump>,
    sqop: &SquirrelData<'a>,
    type_map: &SortFinder<'bump>,
    symbs: implvec!(&'b Fun2<'a>),
) -> HashMap<Fun2<'a>, Apply<'bump, 'a>>
where
    'a: 'b,
{
    symbs
        .into_iter()
        .filter(|x| !matches!(x, Fun2::Diff))
        .map(|f| match f {
            Fun2::Diff => unreachable!(),
            Fun2::Name(n) => {
                let name = container.find_free_function_name(n.as_ref());
                let sqname = sqop
                    .names
                    .get(n.as_ref())
                    .ok_or(ConversiontError::UndeclaredOp)
                    .unwrap();
                let input_sorts = sqname.args.iter().map(|x| type_map.get_sort(x).unwrap());
                let nf =
                    Function::new_user_term_algebra(container, name, input_sorts, NAME.clone());
                (f, nf)
            }
            Fun2::Macro(m) => {
                // container.
                todo!()
            }
            Fun2::Step(_) => todo!(),
            Fun2::Fun(_) => todo!(),
            Fun2::Tuple => todo!(),
            Fun2::ProjL => todo!(),
            Fun2::ProjR => todo!(),
            Fun2::Empty => todo!(),
        });
    todo!()
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
enum Which<T> {
    /// all protocols at once
    Any,
    /// just the protocol defined by the `usize`.
    One(usize, T),
}
