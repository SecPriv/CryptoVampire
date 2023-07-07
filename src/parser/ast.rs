use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use derivative::Derivative;
use itertools::Itertools;
use pest::{error::Error, iterators::Pair, Parser, Span};
use pest_derive::Parser;

use crate::{destvec, formula::variable};

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;

#[inline(always)]
fn err<E:std::error::Error, T>(err: E) -> Result<T, E> {
    if cfg!(debug_assertions) {
        Err(err).unwrap()
    } else {
        Err(err)
    }
}

macro_rules! merr {
    ($span:expr; $msg:literal $(,$args:expr)*) => {
        Error::new_from_span(
            pest::error::ErrorVariant::CustomError {
                message: format!($msg $(,$args)*),
            },
            $span,
        )
    };
}

macro_rules! debug_rule {
    ($p:ident, $($rule:ident)|+) => {
        if cfg!(debug_assertions) && match $p.as_rule() {
                $(Rule::$rule)|+ => false,
                _ => true
            }
         {
            return err(Error::new_from_span(
                pest::error::ErrorVariant::ParsingError {
                    positives: vec![$(Rule::$rule),+],
                    negatives: vec![$p.as_rule()],
                },
                $p.as_span(),
            ));
        }
    };
}

macro_rules! boiler_plate {
    ($t:ty, $lt:lifetime, $($rule:ident)|+; |$p:ident| $content:block) => {
        impl<$lt> TryFrom<Pair<$lt, Rule>> for $t {
            type Error = E;

            fn try_from($p: Pair<$lt, Rule>) -> Result<$t, Self::Error> {
                debug_rule!($p, $($rule)|+);

                $content
            }
        }
    };

    ($t:ty, $rule:ident; |$p:ident| { $($pat:ident => $content:block)* }) => {
        boiler_plate!($t, 'a, $rule; |p| {
            let span = p.as_span();
            let mut p_iter = p.into_inner();
            let $p = p_iter.next().unwrap();

            if let Some(p) = p_iter.next() {
                return err(merr!(p.as_span(); "too much"))
            }

            match $p.as_rule() {
                $(
                    Rule::$pat => $content,
                )*
                r => err(Error::new_from_span(
                pest::error::ErrorVariant::ParsingError {
                    positives: vec![$(Rule::$pat),*],
                    negatives: vec![r],
                },
                span,
            ))
            }
        });
    };

    ($t:ty, $rule:ident; { $($pat:ident => $res:ident),* }) => {
        boiler_plate!($t, $rule; |p| {$($pat => { Ok(Self::$res) })*});
    }

}

macro_rules! as_array {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        destvec!{ [$($arg),*] = $vec; |err| {
            return Err(merr!($span; "{}", err))
        }}
    };
}

mod macro_helper {
    use pest::iterators::{Pairs, Pair};

    use super::Rule;

    pub trait AsInner<'a> {
        fn m_into_inner(self) -> Pairs<'a, Rule>;
    }

    impl<'a> AsInner<'a> for Pairs<'a, Rule>{
        fn m_into_inner(self) -> Pairs<'a, Rule> {
            self
        }
    }

    impl<'a> AsInner<'a> for Pair<'a, Rule> {
        fn m_into_inner(self) -> Pairs<'a, Rule> {
            self.into_inner()
        }
    }
}

macro_rules! dest_rule {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        as_array!($span in [$($arg),*] = macro_helper::AsInner::m_into_inner($vec));
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


// -----------------------------------------------------------------------------
// ---------------------------------- terms ------------------------------------
// -----------------------------------------------------------------------------

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Term<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    inner: InnerTerm<'a>,
}
boiler_plate!(Term<'s>, 's, term; |p| {
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
boiler_plate!(InnerTerm<'s>, 's, inner_term; |p| {
    let span = p.as_span();
    as_array!(span in [nxt] = p.into_inner());
    match nxt.as_rule() {
        Rule::infix_term => {
            dest_rule!(span in [inner] = nxt.into_inner());
            Ok(InnerTerm::Infix(Box::new(inner)))
        }
        Rule::commun_base => {
            as_array!(span in [cmn_rule] = nxt.into_inner());
            match cmn_rule.as_rule(){
                Rule::let_in => {
                    dest_rule!(span in [inner] = cmn_rule.into_inner());
                    Ok(InnerTerm::LetIn(Box::new(inner)))
                },
                Rule::if_then_else => {
                    dest_rule!(span in [inner] = cmn_rule.into_inner());
                    Ok(InnerTerm::If(Box::new(inner)))
                },
                Rule::find_such_that => {
                    dest_rule!(span in [inner] = cmn_rule.into_inner());
                    Ok(InnerTerm::Fndst(Box::new(inner)))
                },
                Rule::quantifier => {
                    dest_rule!(span in [inner] = cmn_rule.into_inner());
                    Ok(InnerTerm::Quant(Box::new(inner)))
                },
                Rule::application => {
                    dest_rule!(span in [inner] = cmn_rule.into_inner());
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
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

boiler_plate!(Operation, operation; {
    hard_eq => HardEq,
    eq => Eq,
    neq => Neq,
    or => Or,
    and => And,
    implies => Implies,
    iff => Iff
});

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
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        span: Span<'a>,
        content: &'a str,
    },
    Application {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
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
boiler_plate!(Quantifier<'a>, 'a, quantifier; |p| {
    let span = p.as_span();
    dest_rule!(span in [kind, vars, content] = p.into_inner());
    Ok(Self { kind, vars, span, content})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum QuantifierKind {
    Forall,
    Exists,
}
boiler_plate!(QuantifierKind, quantifier_op; {
    forall => Forall,
    exists => Exists
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct LetIn<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    var: Variable<'a>,
    t1: Term<'a>,
    t2: Term<'a>,
}
boiler_plate!(LetIn<'a>, 'a, let_in; |p| {
    let span = p.as_span();
    dest_rule!(span in [var, t1, t2] = p.into_inner());
    Ok(Self { span, var, t1, t2})
});

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
boiler_plate!(Assignements<'a>, 'a, assignements; |p| {
    let span = p.as_span();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, assignements })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Assignement<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    cell: Application<'a>,
    term: Term<'a>,
}
boiler_plate!(Assignement<'a>, 'a, assignement; |p| {
    let span = p.as_span();
    dest_rule!(span in [cell, term] = p);
    Ok(Self { span, cell, term })
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
boiler_plate!(Let<'a>, 'a, mlet ; |p| {
    let span = p.as_span();
    dest_rule!(span in [name, args, term] = p);
    Ok(Self {span, name, args, term})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Assert<'a> {
    Assertion(Assertion<'a>),
    Query(Assertion<'a>),
    Lemma(Assertion<'a>),
}
boiler_plate!(Assert<'a>, 'a, assertion | query | lemma ; |p| {
    Ok(match p.as_rule() {
        Rule::assertion => Assert::Assertion(p.try_into()?),
        Rule::query => Assert::Query(p.try_into()?),
        Rule::lemma => Assert::Lemma(p.try_into()?),
        _ => unreachable!()
    })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Assertion<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    span: Span<'a>,
    content: Term<'a>,
}
boiler_plate!(Assertion<'a>, 'a, assertion | query | lemma ; |p| {
    let span = p.as_span();
    dest_rule!(span in [content] = p);
    Ok(Self {span, content})
});