use std::borrow::Cow;

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
use itertools::{chain, Itertools};
use utils::{implvec, iter_array::IntoArray, string_ref::StrRef};

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

type SortsMap<'a> = HashMap<StrRef<'a>, StrRef<'a>>;
type FunsMap<'a> = HashMap<Fun2<'a>, StrRef<'a>>;

#[derive(Debug)]
struct Ctx<'a> {
    sorts: SortsMap<'a>,
    funs: FunsMap<'a>,
    flatten_tuple: HashSet<Fun2<'a>>,
}

impl<'a> Ctx<'a> {
    pub fn flatten_tuple(&self, f: &Fun2<'a>) -> bool {
        self.flatten_tuple.contains(f)
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

fn flatten_args<U:Clone, const N: usize>(arg: [Vec<U>; N]) -> Vec<[U; N]> {
    if N == 0 {
        return vec![];
    } else {
        let max_diff = arg.iter().map(|e| e.len()).max().unwrap(); // because N != 0
        assert!(
            arg.iter().all(|e| !e.is_empty()),
            "empty diffs are not supported"
        );
        (0..max_diff)
            .into_iter()
            .map(|i| std::array::from_fn(|j| arg[i][j].clone()))
            .collect()
    }
}

type Term<'a> = ast::Term<'static, StrRef<'a>>;

trait CollectArgArray<'a> {
    fn collect_arg_array<const N: usize>(
        self,
        ctx: &Ctx<'a>,
        which_diff: Option<usize>,
    ) -> MResult<[Term<'a>; N]>;
}
impl<'a, I> CollectArgArray<'a> for I
where
    I: IntoIterator<Item = TF2<'a>>,
{
    fn collect_arg_array<const N: usize>(
        self,
        ctx: &Ctx<'a>,
        which_diff: Option<usize>,
    ) -> MResult<[Term<'a>; N]> {
        let tmp: std::result::Result<MResult<[ast::Term<_>; N]>, _> = self
            .into_iter()
            .map(|t| convert_term(ctx, which_diff, t))
            .collect_array_exact();
        tmp?
    }
}

fn convert_term<'a>(ctx: &Ctx<'a>, which_diff: Option<usize>, t: TF2<'a>) -> MResult<Term<'a>> {
    let span = Location::default();

    let inner = match t {
        BaseFormula::Binder { head, vars, args } => {
            let vars: Option<TypedArgument<_>> = vars
                .into_iter()
                .map(|x| Some((x.name(), get_sort_str(&ctx.sorts, x.sort.as_ref())?)))
                .collect();
            let vars = vars.with_location(&span)?;
            match head {
                super::SQuant::Forall | super::SQuant::Exists => {
                    let [content]: [ast::Term<_>; 1] = args.collect_arg_array(ctx, which_diff)?;
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
                    let [condition, left, right]: [_; 3] =
                        args.collect_arg_array(ctx, which_diff)?;
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
        BaseFormula::Var(v) => ast::InnerTerm::Application(Box::new(ast::Application::ConstVar {
            span,
            content: v.name().into(),
        })),
        BaseFormula::App { head, args } => {
            if let Fun2::Diff = head {}
            /*
             TODO:
             - a map from `head` to cv function
             - recognising macros
             - recognising function with tuple as arguments
            */

            todo!()
        }
    };

    Ok(ast::Term { span, inner })
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
