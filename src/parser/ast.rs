use std::{fmt::Display, slice::Iter};

use derivative::Derivative;
use itertools::Itertools;
use pest::{error::Error, iterators::Pair, Parser, Span};

use crate::destvec;

use super::*;

macro_rules! unreachable_rules {
    ($span:expr, $urule:expr; $($rule:ident),* ) => {
        return err(Error::new_from_span(
            pest::error::ErrorVariant::ParsingError {
                positives: vec![$(Rule::$rule),+],
                negatives: vec![$urule],
            },
            $span,
        ))
    };
}

macro_rules! debug_rule {
    ($p:ident, $($rule:ident)|+) => {
        if cfg!(debug_assertions) && match $p.as_rule() {
                $(Rule::$rule)|+ => false,
                _ => true
            }
        {
            unreachable_rules!($p.as_span(),  $p.as_rule(); $($rule),*);
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

    (l $t:ty, $lt:lifetime, $($rule:ident)|+; |$p:ident| { $($($pat:ident)|+ => $content:block)* }) => {
        boiler_plate!($t, 'a, $($rule)|+; |p| {
            let span = p.as_span();
            let mut p_iter = p.into_inner();
            let $p = p_iter.next().unwrap();

            if let Some(p) = p_iter.next() {
                return err(merr!(p.as_span(); "too much"))
            }

            match $p.as_rule() {
                $(
                    $(Rule::$pat)|+ => $content,
                )*
                r => unreachable_rules!(span, r; $($($pat),+),*)
            }
        });
    };

    ($t:ty, $rule:ident; { $($pat:ident => $res:ident),* }) => {
        boiler_plate!(l $t, 'a, $rule; |p| {$($pat => { Ok(Self::$res) })*});
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
    use pest::iterators::{Pair, Pairs};

    use super::Rule;

    pub trait AsInner<'a> {
        fn m_into_inner(self) -> Pairs<'a, Rule>;
    }

    impl<'a> AsInner<'a> for Pairs<'a, Rule> {
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ASTList<'a>(pub Vec<AST<'a>>);

impl<'a> TryFrom<&'a str> for ASTList<'a> {
    type Error = E;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        Ok(ASTList(
            MainParser::parse(Rule::file, value)?
                .map(TryInto::try_into)
                .try_collect()?,
        ))
    }
}

impl<'str, 'b> IntoIterator for &'b ASTList<'str> {
    type Item = &'b AST<'str>;

    type IntoIter = Iter<'b, AST<'str>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Sub<'s, T> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'s>,
    pub content: T,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AST<'a> {
    Declaration(Box<Declaration<'a>>),
    Step(Box<Step<'a>>),
    Order(Box<Order<'a>>),
    AssertCrypto(Box<AssertCrypto<'a>>),
    Assert(Box<Assert<'a>>),
    Let(Box<Let<'a>>),
}
boiler_plate!(l AST<'a>, 'a, content; |p| {
    declaration => { Ok(AST::Declaration(Box::new(p.try_into()?))) }
    step => { Ok(AST::Step(Box::new(p.try_into()?))) }
    order => { Ok(AST::Order(Box::new(p.try_into()?))) }
    assertion_crypto => { Ok(AST::AssertCrypto(Box::new(p.try_into()?))) }
    assertion | query | lemma => { Ok(AST::Assert(Box::new(p.try_into()?))) }
    mlet => { Ok(AST::Let(Box::new(p.try_into()?))) }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Ident<'s> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'s>,
    pub content: &'s str,
}
boiler_plate!(Ident<'s>, 's, ident; |p| {
    Ok(Ident { span: p.as_span(), content: p.as_str()})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeName<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(TypeName<'a>, 'a, type_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Function<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(Function<'a>, 'a, function; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable<'a>(pub Sub<'a, &'a str>);
boiler_plate!(Variable<'a>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.as_str() }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct StepName<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(StepName<'a>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VariableBinding<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub variable: Variable<'a>,
    pub type_name: TypeName<'a>,
}
boiler_plate!(VariableBinding<'s>, 's, variable_binding; |p| {
    let span = p.as_span();
    dest_rule!(span in [variable, type_name] = p.into_inner());
    Ok(VariableBinding{span, variable, type_name})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypedArgument<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub bindings: Vec<VariableBinding<'a>>,
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
pub struct Term<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub inner: InnerTerm<'a>,
}
boiler_plate!(Term<'s>, 's, term; |p| {
    let span = p.as_span();
    dest_rule!(span in [inner] = p.into_inner());
    Ok(Term{span, inner})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum InnerTerm<'a> {
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
                r => unreachable_rules!(span, r; let_in, if_then_else, find_such_that, quantifier, application)
            }
        },
        r => unreachable_rules!(span, r; infix_term, commun_base)
    }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Infix<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub operation: Operation,
    pub terms: Vec<Term<'a>>,
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
pub enum Operation {
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
pub enum Application<'a> {
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
pub struct IfThenElse<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub condition: Term<'a>,
    pub left: Term<'a>,
    pub right: Term<'a>,
}
boiler_plate!(IfThenElse<'a>, 'a, if_then_else; |p| {
    let span = p.as_span();
    dest_rule!(span in [condition, left, right] = p.into_inner());
    Ok(IfThenElse { span, condition, left, right})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FindSuchThat<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub vars: TypedArgument<'a>,
    pub condition: Term<'a>,
    pub left: Term<'a>,
    pub right: Term<'a>,
}
boiler_plate!(FindSuchThat<'a>, 'a, find_such_that; |p| {
    let span = p.as_span();
    dest_rule!(span in [vars, condition, left, right] = p.into_inner());
    Ok(Self { vars, span, condition, left, right})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'a> {
    pub kind: QuantifierKind,
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub vars: TypedArgument<'a>,
    pub content: Term<'a>,
}
boiler_plate!(Quantifier<'a>, 'a, quantifier; |p| {
    let span = p.as_span();
    dest_rule!(span in [kind, vars, content] = p.into_inner());
    Ok(Self { kind, vars, span, content})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum QuantifierKind {
    Forall,
    Exists,
}
boiler_plate!(QuantifierKind, quantifier_op; {
    forall => Forall,
    exists => Exists
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct LetIn<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub var: Variable<'a>,
    pub t1: Term<'a>,
    pub t2: Term<'a>,
}
boiler_plate!(LetIn<'a>, 'a, let_in; |p| {
    let span = p.as_span();
    dest_rule!(span in [var, t1, t2] = p.into_inner());
    Ok(Self { span, var, t1, t2})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Declaration<'a> {
    Type(DeclareType<'a>),
    Function(DeclareFunction<'a>),
    Cell(DeclareCell<'a>),
}
boiler_plate!(l Declaration<'a>, 'a, declaration; |p| {
    declare_type => { Ok(Declaration::Type(p.try_into()?)) }
    declare_function => { Ok(Declaration::Function(p.try_into()?)) }
    declare_cell => { Ok(Declaration::Cell(p.try_into()?)) }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareType<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: TypeName<'a>,
}
boiler_plate!(DeclareType<'a>, 'a, declare_type; |p| {
    let span = p.as_span();
    dest_rule!(span in [name] = p);
    Ok(Self { span, name })
});

impl<'a> DeclareType<'a> {
    pub fn name(&self) -> &'a str {
        self.name.0.content.content
    }

    pub fn get_name_span(&self) -> &Span<'a> {
        &self.name.0.span
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunction<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: Function<'a>,
    pub args: DeclareFunctionArgs<'a>,
    pub sort: TypeName<'a>,
}
boiler_plate!(DeclareFunction<'a>, 'a, declare_function; |p| {
    let span = p.as_span();
    dest_rule!(span in [name, args, sort] = p);
    Ok(Self { span, name, args, sort })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunctionArgs<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub args: Vec<TypeName<'a>>,
}
boiler_plate!(DeclareFunctionArgs<'a>, 'a, declare_function_args; |p| {
    let span = p.as_span();
    let args = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, args })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: Function<'a>,
    pub args: DeclareFunctionArgs<'a>,
    pub sort: TypeName<'a>,
}
boiler_plate!(DeclareCell<'a>, 'a, declare_cell; |p| {
    let span = p.as_span();
    dest_rule!(span in [name, args, sort] = p);
    Ok(Self { span, name, args, sort })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Step<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: StepName<'a>,
    pub args: TypedArgument<'a>,
    pub condition: Term<'a>,
    pub message: Term<'a>,
    pub assignements: Option<Assignements<'a>>,
}
boiler_plate!(Step<'a>, 'a, step; |p| {
    let span = p.as_span();
    // dest_rule!(span in [name, args, condition, message, assignements] = p);
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let args = p.next().unwrap().try_into()?;
    let condition = p.next().unwrap().try_into()?;
    let message = p.next().unwrap().try_into()?;
    let assignements = p.next().map(TryInto::try_into).transpose()?;

    if let Some(np) = p.next() {
        let mut l = 0;
        for _ in p {
            l+=1;
        }
        return err(merr!(np.as_span();
            "too many arguments (expected at most 5, got {})",
            (6 + l)))
    }

    Ok(Self { span, name, args, condition, message, assignements})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignements<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub assignements: Vec<Assignement<'a>>,
}
boiler_plate!(Assignements<'a>, 'a, assignements; |p| {
    let span = p.as_span();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, assignements })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub cell: Application<'a>,
    pub term: Term<'a>,
}
boiler_plate!(Assignement<'a>, 'a, assignement; |p| {
    let span = p.as_span();
    dest_rule!(span in [cell, term] = p);
    Ok(Self { span, cell, term })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Let<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: Function<'a>,
    pub args: TypedArgument<'a>,
    pub term: Term<'a>,
}
boiler_plate!(Let<'a>, 'a, mlet ; |p| {
    let span = p.as_span();
    dest_rule!(span in [name, args, term] = p);
    Ok(Self {span, name, args, term})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Assert<'a> {
    Assertion(Assertion<'a>),
    Query(Assertion<'a>),
    Lemma(Assertion<'a>),
}
boiler_plate!(l Assert<'a>, 'a, assertion | query | lemma ; |p| {
    assertion => { Ok(Assert::Assertion(p.try_into()?)) }
    query => { Ok(Assert::Query(p.try_into()?)) }
    lemma => { Ok(Assert::Lemma(p.try_into()?)) }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assertion<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub content: Term<'a>,
}
boiler_plate!(Assertion<'a>, 'a, assertion | query | lemma ; |p| {
    let span = p.as_span();
    dest_rule!(span in [content] = p);
    Ok(Self {span, content})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AssertCrypto<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: Ident<'a>,
    pub functions: Vec<Function<'a>>,
}
boiler_plate!(AssertCrypto<'a>, 'a, assertion_crypto ; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let functions = p.map(TryInto::try_into).try_collect()?;

    Ok(Self {span, name, functions})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Order<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub quantifier: QuantifierKind,
    pub args: TypedArgument<'a>,
    pub t1: Term<'a>,
    pub t2: Term<'a>,
    pub kind: OrderOperation,
}
boiler_plate!(Order<'a>, 'a, order ; |p| {
    let span = p.as_span();
    dest_rule!(span in [quantifier, args, t1, kind, t2] = p);
    Ok(Self {span, quantifier, args, t1, t2, kind})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum OrderOperation {
    Incompatible,
    Lt,
    Gt,
}
boiler_plate!(OrderOperation, operation; {
    order_incompatible => Incompatible,
    order_lt => Lt,
    order_gt => Gt
});

pub mod extra {
    use enum_dispatch::enum_dispatch;
    use pest::Span;

    use crate::formula::sort::builtins::STEP;

    use super::{DeclareCell, DeclareFunction, Function, Step, StepName, TypeName};

    #[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
    pub struct SnN<'a, 'b> {
        span: &'b Span<'a>,
        name: &'a str,
    }

    impl<'a, 'b> From<&'b TypeName<'a>> for SnN<'a, 'b> {
        fn from(value: &'b TypeName<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content,
            }
        }
    }

    impl<'a, 'b> From<&'b Function<'a>> for SnN<'a, 'b> {
        fn from(value: &'b Function<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content,
            }
        }
    }

    impl<'a, 'b> From<&'b StepName<'a>> for SnN<'a, 'b> {
        fn from(value: &'b StepName<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content,
            }
        }
    }

    #[enum_dispatch]
    pub trait AsFunction<'a> {
        fn name(&'_ self) -> SnN<'a, '_>;
        fn args(&'_ self) -> Vec<SnN<'a, '_>>;
        fn out(&'_ self) -> SnN<'a, '_>;
    }

    impl<'a> AsFunction<'a> for DeclareFunction<'a> {
        fn name(&'_ self) -> SnN<'a, '_> {
            From::from(&self.name)
        }

        fn args(&'_ self) -> Vec<SnN<'a, '_>> {
            self.args.args.iter().map(|tn| tn.into()).collect()
        }

        fn out(&'_ self) -> SnN<'a, '_> {
            From::from(&self.sort)
        }
    }

    impl<'a> AsFunction<'a> for DeclareCell<'a> {
        fn name(&'_ self) -> SnN<'a, '_> {
            From::from(&self.name)
        }

        fn args(&'_ self) -> Vec<SnN<'a, '_>> {
            self.args
                .args
                .iter()
                .map(|tn| tn.into())
                .chain([SnN {
                    span: &self.span,
                    name: STEP.name(),
                }])
                .collect()
        }

        fn out(&'_ self) -> SnN<'a, '_> {
            From::from(&self.sort)
        }
    }

    impl<'a> AsFunction<'a> for Step<'a> {
        fn name(&'_ self) -> SnN<'a, '_> {
            From::from(&self.name)
        }

        fn args(&'_ self) -> Vec<SnN<'a, '_>> {
            self.args
                .bindings
                .iter()
                .map(|b| From::from(&b.type_name))
                .collect()
        }

        fn out(&'_ self) -> SnN<'a, '_> {
            SnN {
                span: &self.span,
                name: STEP.name(),
            }
        }
    }
}
