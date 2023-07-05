use std::collections::{HashMap, HashSet};

use paste::paste;
use pest::{error::Error, iterators::Pair, Parser};
use pest_derive::Parser;

use crate::{
    container::Container,
    formula::{formula::RichFormula, function::Function, sort::Sort},
    utils::string_ref::StrRef,
};

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;

macro_rules! merr {
    ($span:ident; $msg:literal $(,$args:expr)*) => {
        Error::new_from_span(
            pest::error::ErrorVariant::CustomError {
                message: format!($msg $(,$args)*),
            },
            $span,
        )
    };
}

macro_rules! debug_rule {
    ($p:ident, $rule:ident) => {
        if cfg!(debug_assertions) && !matches!($p.as_rule(), Rule::$rule) {
            return Err(Error::new_from_span(
                pest::error::ErrorVariant::ParsingError {
                    positives: vec![Rule::$rule],
                    negatives: vec![$p.as_rule()],
                },
                $p.as_span(),
            ));
        }
    };
}

macro_rules! boiler_plate {
    ($rule:ident, $out_type:ty; $env:ident, $p:ident $(, $arg:ident: $arg_ty:ty)*; $content:block) => {
        paste! {
            fn [< parse_ $rule >]<'str, 'bump: 'str>(
                $env: &mut ParsingEnv<'str, 'bump>,
                $p: Pair<'str, Rule>
                $(, $arg: $arg_ty)*
            ) -> Result<$out_type, E> {
                debug_rule!($p, $rule);

                $content
            }
        }
    };
}

#[derive(Debug, Clone)]
struct ParsingEnv<'str, 'bump>
where
    'bump: 'str,
{
    container: &'bump Container<'bump>,
    variables: Vec<(&'str str, RichFormula<'bump>)>,
    used_names: HashSet<StrRef<'str>>,
    used_sort_name: HashSet<StrRef<'str>>,
}

impl<'str, 'bump> ParsingEnv<'str, 'bump>
where
    'bump: 'str,
{
    fn new(container: &'bump Container<'bump>) -> Self {
        Self {
            container,
            variables: vec![],
            used_names: container.name_hash_set(),
            used_sort_name: todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct DeclareSort<'str> {
    name: &'str str,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct DeclareFun<'str, 'bump> {
    name: &'str str,
    args: Vec<Sort<'bump>>,
    out: Sort<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum Declaration<'str, 'bump> {
    Sort(DeclareSort<'str>),
    Function(DeclareFun<'str, 'bump>),
}

pub fn parse_string(str: &str) -> Result<(), E> {
    let p = MainParser::parse(Rule::content, str)?.next().unwrap();
    let env = todo!();
    parse_content(env, p)?;

    todo!()
}

boiler_plate!(content, (); env, p;{

    let p = p.into_inner();

    for p in p {
        match p.as_rule() {
            Rule::declaration => {parse_declaration(env, p)?;},
            _ => todo!()
        }
    }

    todo!()
});

boiler_plate!(ident, &'str str; _env, p; {Ok(p.as_str())});

boiler_plate!(declaration, Declaration<'str, 'bump>; env, p; {
    let p = p.into_inner().next().unwrap(); // can't fail

    let r  = match p.as_rule() {
        Rule::declare_type => {
            Declaration::Sort(parse_declare_type(env, p)?)
        },
        Rule::declare_function => todo!(),
        Rule::declare_cell => todo!(),
        _ => unreachable!(),
    };
    Ok(r)
});

boiler_plate!(declare_type, DeclareSort<'str>; env, p; {
    let mut p = p.into_inner();

    let type_name = p.next().unwrap();
    let type_name_span = type_name.as_span();
    let name = parse_type_name(env, type_name)?;

    if env.used_sort_name.contains(&name.into()) {
        Err(merr!(type_name_span; "the name {} is already taken", name))
    } else {
        Ok(DeclareSort { name })
    }
});

boiler_plate!(type_name, &'str str; env, p; {
    let p = p.into_inner().next().unwrap(); // can't fail
    parse_ident(env, p)
});
