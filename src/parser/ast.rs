use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use derivative::Derivative;
use paste::paste;
use pest::{error::Error, iterators::Pair, Parser, Span};
use pest_derive::Parser;

use crate::{destvec, formula::variable};

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
    ($t:ty, $lt:lifetime, $rule:ident; |$p:ident| $content:block) => {
        impl<$lt> TryFrom<Pair<$lt, Rule>> for $t {
            type Error = E;

            fn try_from($p: Pair<$lt, Rule>) -> Result<$t, Self::Error> {
                debug_rule!($p, $rule);

                $content
            }
        }
    };
    
    ($t:ty, $rule:ident; { $($pat:ident => $res:ident),* }) => {
        boiler_plate!($t, 'a, $rule; |p| {
            match p.as_rule() {
                $(
                    Rule::$pat => Ok(Self::$res),
                )*
                r => Err(Error::new_from_span(

                ))
            }
        })
    }
    
}

macro_rules! as_array {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        destvec!{ [$($arg),*] = $vec; |err| {
            return Err(merr!($span; "{}", err))
        }}
    };
}

macro_rules! dest_rule {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        as_array!($span in [$($arg),*] = $vec);
        $(
            let $arg = $arg.try_into()?;
        )*
    };
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Sub<'s, T> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'s>,
    content: T,
}

#[derive(Derivative)]
#[derivative(
    Debug,
    PartialEq,
    Eq,
    PartialOrd = "feature_allow_slow_enum",
    Ord = "feature_allow_slow_enum",
    Hash,
    Clone
)]
enum AST<'a> {
    Declaration(Box<Declaration<'a>>),
    Step(Box<Step<'a>>),
    Order,
    AssertCrypto,
    Assert(Box<Assert<'a>>),
    Let(Box<Let<'a>>),
}

boiler_plate!(AST<'a>, 'a, content; |p| {
    todo!()
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Let<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    name: Function<'a>,
    args: TypedArgument<'a>,
    term: Term<'a>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Assert<'a> {
    Assertion(Assertion<'a>),
    Query(Assertion<'a>),
    Lemma(Assertion<'a>),
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Assertion<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    content: Term<'a>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Ident<'s> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'s>,
    content: &'s str,
}
boiler_plate!(Ident<'s>, 's, ident; |p| {
    Ok(Ident { span: p.as_span(), content: p.as_str()})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct TypeName<'a>(Sub<'a, Ident<'a>>);
boiler_plate!(TypeName<'a>, 'a, type_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Function<'a>(Sub<'a, Ident<'a>>);
boiler_plate!(Function<'a>, 'a, function; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Variable<'a>(Sub<'a, &'a str>);
boiler_plate!(Variable<'a>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.as_str() }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct StepName<'a>(Sub<'a, Ident<'a>>);
boiler_plate!(StepName<'a>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct VariableBinding<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    variable: Variable<'a>,
    type_name: TypeName<'a>,
}
boiler_plate!(VariableBinding<'s>, 's, variable_binding; |p| {
    let span = p.as_span();
    dest_rule!(span in [variable, type_name] = p.into_inner());
    Ok(VariableBinding{span, variable, type_name})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct TypedArgument<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    bindings: Vec<VariableBinding<'a>>,
}
boiler_plate!(TypedArgument<'a>, 'a, typed_arguments; |p| {
    let span = p.as_span();
    let bindings : Result<Vec<_>, _> = p.into_inner().map(TryInto::try_into).collect();
    Ok(TypedArgument { span, bindings: bindings? })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Term<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    inner: InnerTerm<'a>,
}
boiler_plate!(VariableBinding<'s>, 's, term; |p| {
    let span = p.as_span();
    dest_rule!(span in [inner] = p.into_inner());
    Ok(Term{span, inner})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum InnerTerm<'a> {
    LetIn(Box<LetIn<'a>>),
    If(Box<IfThenElse<'a>>),
    Fndst(Box<FindSuchThat<'a>>),
    Quant(Box<Quantifier<'a>>),
    Appliction(Box<Application<'a>>),
    Infix(Box<Infix<'a>>),
}
boiler_plate!(VariableBinding<'s>, 's, inner_term; |p| {
    let span = p.as_span();
    as_array!(span in [nxt] = p.into_inner());
    match nxt.as_rule() {
        Rule::infix_term => {
            dest_rule!(span in [inner] = nxt);
            Ok(InnerTerm::Infix(Box::new(inner)))
        }
        Rule::commun_base => {
            as_array!(span in [cmn_rule] = nxt.into_inner());
            match cmn_rule.as_rule(){
                Rule::let_in => {
                    dest_rule!(span in [inner] = nxt);
                    Ok(InnerTerm::LetIn(Box::new(inner)))
                },
                Rule::if_then_else => {
                    dest_rule!(span in [inner] = nxt);
                    Ok(InnerTerm::If(Box::new(inner)))
                },
                Rule::find_such_that => {
                    dest_rule!(span in [inner] = nxt);
                    Ok(InnerTerm::Fndst(Box::new(inner)))
                },
                Rule::quantifier => {
                    dest_rule!(span in [inner] = nxt);
                    Ok(InnerTerm::Quant(Box::new(inner)))
                },
                Rule::application => {
                    dest_rule!(span in [inner] = nxt);
                    Ok(InnerTerm::Appliction(Box::new(inner)))
                },
                _ => unreachable!()
            }
        },
        _ => unreachable!()
    }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Infix<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    operation: Operation,
    terms: Vec<Term<'a>>,
}
boiler_plate!(Infix<'a>, 'a, infix_term; |p| {
    let span = p.as_span();
    let mut terms = Vec::new();

    let mut p = p.into_inner();

    terms.push(p.next().unwrap().try_into()?);
    let operation : Operation = p.next().unwrap().try_into()?;
    terms.push(p.next().unwrap().try_into()?);

    while let Some(n_op) = p.next() {
        let n_op_span = n_op.as_span();
        if n_op.try_into() != Ok(operation) {
            return Err(merr!(n_op_span; "should be {}", operation))
        }
        terms.push(p.next().unwrap().try_into()?)
    }
    Ok(Infix { span, operation, terms })
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Operation {
    HardEq,
    Eq,
    Neq,
    Or,
    And,
    Implies,
    Iff,
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::HardEq => "===",
            Operation::Eq => "==",
            Operation::Neq => "!=",
            Operation::Or => "||",
            Operation::And => "&&",
            Operation::Implies => "=>",
            Operation::Iff => "<=>",
        }
        .fmt(f)
    }
}

impl<'str> TryFrom<Pair<'str, Rule>> for Operation {
    type Error = E;

    fn try_from(value: Pair<'str, Rule>) -> Result<Self, Self::Error> {
        let span = value.as_span();
        match value.as_rule() {
            Rule::hard_eq => Ok(Self::HardEq),
            Rule::eq => Ok(Self::Eq),
            Rule::neq => Ok(Self::Neq),
            Rule::or => Ok(Self::Or),
            Rule::and => Ok(Self::And),
            Rule::implies => Ok(Self::Implies),
            Rule::iff => Ok(Self::Iff),
            r => Err(Error::new_from_span(
                pest::error::ErrorVariant::ParsingError {
                    positives: vec![
                        Rule::hard_eq,
                        Rule::eq,
                        Rule::neq,
                        Rule::neq,
                        Rule::or,
                        Rule::and,
                        Rule::implies,
                        Rule::iff,
                    ],
                    negatives: vec![r],
                },
                span,
            )),
        }
    }
}

#[derive(Derivative)]
#[derivative(
    Debug,
    PartialEq,
    Eq,
    PartialOrd = "feature_allow_slow_enum",
    Ord = "feature_allow_slow_enum",
    Hash,
    Clone
)]
enum Application<'a> {
    ConstVar {
        span: Span<'a>,
        content: &'a str,
    },
    Application {
        span: Span<'a>,
        function: Function<'a>,
        args: Vec<Term<'a>>,
    },
}
boiler_plate!(Application<'a>, 'a, application; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let name = p.next().unwrap();

    if let None = p.peek() {
        Ok(Application::ConstVar { span, content: name.as_str() })
    } else {
        let args : Result<Vec<_>, _> = p.map(TryInto::try_into).collect();
        Ok(Application::Application { span, function: name.try_into()?, args: args? })
    }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct IfThenElse<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    condition: Term<'a>,
    left: Term<'a>,
    right: Term<'a>,
}
boiler_plate!(IfThenElse<'a>, 'a, if_then_else; |p| {
    let span = p.as_span();
    dest_rule!(span in [condition, left, right] = p.into_inner());
    Ok(IfThenElse { span, condition, left, right})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct FindSuchThat<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    vars: TypedArgument<'a>,
    condition: Term<'a>,
    left: Term<'a>,
    right: Term<'a>,
}
boiler_plate!(FindSuchThat<'a>, 'a, find_such_that; |p| {
    let span = p.as_span();
    dest_rule!(span in [vars, condition, left, right] = p.into_inner());
    Ok(Self { vars, span, condition, left, right})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Quantifier<'a> {
    kind: QuantifierKind,
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    vars: TypedArgument<'a>,
    content: Term<'a>,
}
boiler_plate!(Quantifier<'a>, 'a, find_such_that; |p| {
    let span = p.as_span();
    dest_rule!(span in [kind, vars, content] = p.into_inner());
    Ok(Self { kind, vars, span, content})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum QuantifierKind {
    Forall,
    Exits,
}
impl<'a> TryFrom<Pair<'a, Rule>> for QuantifierKind {
    type Error = E;

    fn try_from(value: Pair<'a, Rule>) -> Result<Self, Self::Error> {
        match value.as_rule() {
            Rule::exists => Ok(Self::Exits),
            Rule::forall => Ok(Self::Forall)
        }
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct LetIn<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    var: Variable<'a>,
    t1: Term<'a>,
    t2: Term<'a>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Declaration<'a> {
    Type(DeclareType<'a>),
    Function(DeclareFunction<'a>),
    Cell(DeclareCell<'a>),
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct DeclareType<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    name: TypeName<'a>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct DeclareFunction<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    name: Function<'a>,
    args: Vec<TypeName<'a>>,
    sort: TypeName<'a>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct DeclareCell<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    name: Function<'a>,
    args: Vec<TypeName<'a>>,
    sort: TypeName<'a>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Step<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    name: StepName<'a>,
    args: Vec<TypedArgument<'a>>,
    condition: Term<'a>,
    message: Term<'a>,
    assignements: Option<Assignements<'a>>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Assignements<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    assignements: Vec<Assignement<'a>>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Assignement<'a> {
    cell: Application<'a>,
    term: Term<'a>,
}
