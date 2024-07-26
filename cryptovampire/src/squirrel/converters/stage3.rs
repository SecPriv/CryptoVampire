use std::{borrow::Cow, default, ops::Index, sync::Arc};

use super::Result;
use anyhow::Context;
use cryptovampire_lib::{
    container::{utils::NameFinder, ScopedContainer},
    formula::{
        function::{inner::name::Name, Function},
        sort::{
            self,
            builtins::{BOOL, CONDITION, MESSAGE, NAME, STEP},
            inner::{BOOL_NAME, MESSAGE_NAME},
            Sort,
        },
        variable::uvar,
        BaseFormula,
    },
};
use hashbrown::{HashMap, HashSet};
use if_chain::if_chain;
use itertools::{chain, Itertools};
use utils::{all_or_one::AllOrOne, monad::Monad};
use utils::{
    all_or_one::{AllOrOneShape, AoOV},
    implvec,
    iter_array::IntoArray,
    mdo,
    string_ref::StrRef,
};

use crate::{
    err_at,
    parser::{
        ast::{self, TypedArgument},
        InputError, Location, MResult, WithLocation,
    },
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

// fn try_into_array<A, B, const N: usize>(a: Vec<A>) -> MResult<[B; N]>
// where
//     A: TryInto<B, Error = InputError>,
// {
//     let tmp: std::result::Result<Vec<B>, InputError> =
//         a.into_iter().map(|x| x.try_into()).collect();
//     Ok(tmp?
//         .try_into()
//         .map_err(|_| err_at!(&Location::none(), "wrong number of arguments"))?)
// }

#[derive(Debug, Clone)]
enum FunctionKind<'a> {
    Concrete(StrRef<'a>),
    WithTuple(StrRef<'a>),
    Direct(StrRef<'a>),
}

type SortsMap<'a> = HashMap<StrRef<'a>, StrRef<'a>>;
type FunsMap<'a> = HashMap<Fun2<'a>, FunctionKind<'a>>;
type RAoO<T> = MResult<AoOV<T>>;

#[derive(Debug)]
struct Ctx<'a> {
    sorts: SortsMap<'a>,
    funs: FunsMap<'a>,
}

impl<'a> Ctx<'a> {
    pub fn get_function(&self, f: &Fun2<'a>) -> Option<&FunctionKind<'a>> {
        self.funs.get(f)
    }
    pub fn get_sort(&self, f: &StrRef<'a>) -> Option<&StrRef<'a>> {
        self.sorts.get(f)
    }
}

fn mk_sort_data<'a>(sorts: &[json::Sort<'a>]) -> SortsMap<'a> {
    sorts
        .iter()
        .map(|json::Content { symb, data }| {
            let nsymb: StrRef<'a> = symb.clone().into();
            if data.can_be_index() {
                (nsymb, format!("sq_{symb}").into())
            } else {
                (nsymb.clone(), MESSAGE.name())
            }
        })
        .collect()
}

fn get_sort_str<'a>(sorts: &SortsMap<'a>, symb: &json::Type<'a>) -> Option<StrRef<'a>> {
    match symb {
        json::Type::Message => Some(MESSAGE.name()),
        json::Type::Boolean => Some(BOOL.name()),
        json::Type::Index => Some("index".into()),
        json::Type::Timestamp => Some(STEP.name()),
        json::Type::TBase(s) => sorts.get(s.as_ref()).cloned(),
        json::Type::TVar { .. }
        | json::Type::TUnivar { .. }
        | json::Type::Tuple { .. }
        | json::Type::Fun { .. } => None,
    }
}

type Term<'a> = ast::Term<'static, StrRef<'a>>;

trait CollectArgArray<'a> {
    fn collect_args(self, ctx: &Ctx<'a>, shape: AllOrOneShape) -> RAoO<Vec<Term<'a>>>;

    fn collect_arg_array<const N: usize>(
        self,
        ctx: &Ctx<'a>,
        shape: AllOrOneShape,
    ) -> RAoO<[Term<'a>; N]>
    where
        Self: Sized,
    {
        mdo! {
            l <- self.collect_args(ctx, shape);
            block {
                l.collect_array_exact().map(|arr| AllOrOne::Any(arr)).map_err(|e| e.into())
            }
        }
    }
}
impl<'a, I> CollectArgArray<'a> for I
where
    I: IntoIterator<Item = TF2<'a>>,
{
    fn collect_args(self, ctx: &Ctx<'a>, shape: AllOrOneShape) -> RAoO<Vec<Term<'a>>> {
        let res: Vec<_> = self
            .into_iter()
            .map(|t| convert_term(ctx, shape, t))
            .try_collect()?;
        Ok(AoOV::transpose(res))
    }
}

fn convert_term<'a>(ctx: &Ctx<'a>, shape: AllOrOneShape, t: TF2<'a>) -> RAoO<Term<'a>> {
    let span = Location::default();

    /* let term: RAoO<Term<'a>> = */
    match t {
        BaseFormula::Binder { head, vars, args } => {
            let vars: Option<TypedArgument<_>> = vars
                .into_iter()
                .map(|x| Some((x.name(), get_sort_str(&ctx.sorts, x.sort.as_ref())?)))
                .collect();
            let vars = vars.with_location(&span)?;
            match head {
                super::SQuant::Forall | super::SQuant::Exists => {
                    let kind = match head {
                        super::SQuant::Exists => ast::QuantifierKind::Exists,
                        super::SQuant::Forall => ast::QuantifierKind::Forall,
                        _ => unreachable!(),
                    };
                    mdo! {
                     [content] <- args.collect_arg_array(ctx, shape);
                     pure {ast::Quantifier {
                         span,
                         vars: vars.clone(),
                         kind,
                         content: content.clone(),
                     }.into()}
                    }
                }
                super::SQuant::FindSuchThat => {
                    mdo! {
                        [condition, left, right] <- args.collect_arg_array(ctx, shape);
                        pure {ast::FindSuchThat {
                                span,
                                vars: vars.clone(),
                                condition,
                                left,
                                right,
                            }.into()}
                    }
                }
            }
        }
        BaseFormula::Var(v) => {
            mdo! {
                pure {ast::Application::ConstVar {
                    span,
                    content: v.name().into(),
                }.into()}
            }
        }
        BaseFormula::App { head, mut args } => {
            if let Fun2::Diff = head {
                match shape {
                    AllOrOne::All(_) | AllOrOne::Any(_) => {
                        let vec: Vec<_> = args
                            .into_iter()
                            .enumerate()
                            .map(|(i, t)| convert_term(ctx, AllOrOne::One(i, ()), t))
                            .try_collect()?;
                        Ok(AllOrOne::All(
                            vec.into_iter()
                                .enumerate()
                                .map(|(i, t)| t.owned_get(i))
                                .collect(),
                        ))
                    }
                    AllOrOne::One(i, _) => {
                        let arg = args.swap_remove(i);
                        convert_term(ctx, AllOrOne::One(i, ()), arg)
                    }
                }
            } else {
                match head {
                    Fun2::Name(str) => todo!(),
                    Fun2::Macro(_) => todo!(),
                    Fun2::Step(_) => todo!(),
                    Fun2::Fun(_) => todo!(),
                    Fun2::Tuple => todo!(),
                    Fun2::ProjL => todo!(),
                    Fun2::ProjR => todo!(),
                    Fun2::Diff => todo!(),
                    Fun2::Empty => todo!(),
                }
                match ctx
                    .get_function(&head)
                    .with_context(|| "undeclared function")
                    .with_location(span)?
                {
                    FunctionKind::Concrete(str) => {
                        // ast::AppMacro {span, inner: ast::InnerAppMacro::Other { name: (), args: () }};
                        todo!()
                    }
                    FunctionKind::WithTuple(_) => todo!(),
                    FunctionKind::Direct(_) => todo!(),
                }
            }
            /*
             TODO:
             - a map from `head` to cv function
             - recognising macros
             - recognising function with tuple as arguments
            */

            // todo!()
        }
    }

    // Ok(ast::Term { span, inner })
}

#[derive(Debug)]
struct SquirrelData<'a> {
    pub operators: HashMap<String, json::operator::Data<'a, TF2<'a>, SVariable, json::Type<'a>>>,
    pub types: HashMap<String, json::mtype::SortData>,
    pub actions: HashMap<String, Action<'a, TF2<'a>, SVariable>>,
    pub names: HashMap<String, FunctionType<'a, json::Type<'a>>>,
    pub macros: HashMap<String, json::mmacro::Data<'a, TF2<'a>, json::Type<'a>>>,
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
