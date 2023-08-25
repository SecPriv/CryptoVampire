use std::{fmt::Display, slice::Iter};

use const_format::concatcp;
use derivative::Derivative;
use itertools::Itertools;
use pest::{error::Error, iterators::Pair, Parser, Position, Span};
use static_init::dynamic;

use crate::{destvec, f, problem::step::INIT_STEP_NAME, utils::vecref::VecRef};

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
                return err(merr(p.as_span(), f!("too much")))
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
            return Err(merr($span, f!("{}", err)))
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
            let $arg = $arg.try_into().debug_continue()?;
        )*
    };
}

const INIT_STEP_STRING: &'static str = concatcp!("step ", INIT_STEP_NAME, "(){true}{empty}");

#[dynamic]
pub static INIT_STEP_AST: Step<'static> = {
    let ASTList { content, .. } = INIT_STEP_STRING.try_into().unwrap();
    match content.into_iter().next() {
        Some(AST::Step(s)) => *s,
        _ => unreachable!(),
    }
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ASTList<'a> {
    pub content: Vec<AST<'a>>,
    pub begining: Position<'a>,
}

impl<'a> TryFrom<&'a str> for ASTList<'a> {
    type Error = E;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        let mut pairs = MainParser::parse(Rule::file, value).debug_continue()?;

        Ok(ASTList {
            content: pairs
                .next()
                .unwrap()
                .into_inner()
                .filter(|p| p.as_rule() == Rule::content)
                .map(|p| {
                    debug_print::debug_println!(" --> {}", p.as_str());
                    p.try_into().debug_continue()
                })
                .try_collect()
                .debug_continue()?,
            begining: Position::from_start(value),
        })
    }
}

impl<'str, 'b> IntoIterator for &'b ASTList<'str> {
    type Item = &'b AST<'str>;

    type IntoIter = Iter<'b, AST<'str>>;

    fn into_iter(self) -> Self::IntoIter {
        self.content.iter()
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
    Let(Box<Macro<'a>>),
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
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Ident<'s> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'s>,
    pub content: &'s str,
}
boiler_plate!(Ident<'s>, 's, ident; |p| {
    Ok(Ident { span: p.as_span(), content: p.as_str()})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeName<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(TypeName<'a>, 'a, type_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a> TypeName<'a> {
    pub fn name(&self) -> &'a str {
        self.0.content.content
    }

    pub fn name_span(&self) -> Span<'a> {
        self.0.span
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Function<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(Function<'a>, 'a, function; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a> Function<'a> {
    pub fn name(&self) -> &'a str {
        self.0.content.content
    }

    pub fn span(&self) -> Span<'a> {
        self.0.span
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MacroName<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(MacroName<'a>, 'a, macro_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a> MacroName<'a> {
    pub fn name(&self) -> &'a str {
        self.0.content.content
    }

    pub fn span(&self) -> Span<'a> {
        self.0.span
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable<'a>(pub Sub<'a, &'a str>);
boiler_plate!(Variable<'a>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.as_str() }))
});

impl<'a> Variable<'a> {
    pub fn name(&self) -> &'a str {
        self.0.content
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct StepName<'a>(pub Sub<'a, Ident<'a>>);
boiler_plate!(StepName<'a>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a> StepName<'a> {
    pub fn name(&self) -> &'a str {
        self.0.content.content
    }
}

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
    Application(Box<Application<'a>>),
    Infix(Box<Infix<'a>>),
    Macro(Box<AppMacro<'a>>),
}
boiler_plate!(InnerTerm<'s>, 's, inner_term; |p| {
    let span = p.as_span();
    as_array!(span in [nxt] = p.into_inner());
    match nxt.as_rule() {
        Rule::infix_term => {
            // let mut nxt_inner = nxt.into_inner();
            // debug_print::debug_println!("{:?}", nxt_inner);
            // dest_rule!(span in [inner] = nxt_inner);
            Ok(InnerTerm::Infix(Box::new(nxt.try_into()?)))
        }
        Rule::commun_base => {
            as_array!(span in [cmn_rule] = nxt.into_inner());
            match cmn_rule.as_rule(){
                Rule::let_in => {
                    // dest_rule!(span in [inner] = cmn_rule.into_inner());
                    // Ok(InnerTerm::LetIn(Box::new(inner)))
                    Ok(InnerTerm::LetIn(Box::new(cmn_rule.try_into()?)))
                },
                Rule::if_then_else => {
                    // dest_rule!(span in [inner] = cmn_rule.into_inner());
                    // Ok(InnerTerm::If(Box::new(inner)))
                    Ok(InnerTerm::If(Box::new(cmn_rule.try_into()?)))
                },
                Rule::find_such_that => {
                    // dest_rule!(span in [inner] = cmn_rule.into_inner());
                    // Ok(InnerTerm::Fndst(Box::new(inner)))
                    Ok(InnerTerm::Fndst(Box::new(cmn_rule.try_into()?)))
                },
                Rule::quantifier => {
                    // dest_rule!(span in [inner] = cmn_rule.into_inner());
                    // Ok(InnerTerm::Quant(Box::new(inner)))
                    Ok(InnerTerm::Quant(Box::new(cmn_rule.try_into()?)))
                },
                Rule::application => {
                    // dest_rule!(span in [inner] = cmn_rule.into_inner());
                    // Ok(InnerTerm::Application(Box::new(inner)))
                    Ok(InnerTerm::Application(Box::new(cmn_rule.try_into()?)))
                },
                Rule::macro_application => {
                    // dest_rule!(span in [inner] = cmn_rule.into_inner());
                    // Ok(InnerTerm::Macro(Box::new(inner)))
                    Ok(InnerTerm::Macro(Box::new(cmn_rule.try_into()?)))
                }
                r => unreachable_rules!(span, r; let_in, if_then_else, find_such_that, quantifier, application)
            }
        },
        r => unreachable_rules!(span, r; infix_term, commun_base)
    }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AppMacro<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub inner: InnerAppMacro<'a>,
}

fn from_term_to_application<'a>(p: Pair<'a, Rule>) -> Result<Application<'a>, E> {
    debug_rule!(p, term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, inner_term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, commun_base);
    let p = p.into_inner().next().unwrap();
    p.try_into()
}

boiler_plate!(AppMacro<'a>, 'a, macro_application; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let inner = {
        let name: MacroName = p.next().unwrap().try_into()?;

        match name.0.content.content {
            "msg" => InnerAppMacro::Msg(from_term_to_application(p.next().unwrap())?),
            "cond" => InnerAppMacro::Cond(from_term_to_application(p.next().unwrap())?),
            _ => {
                let args : Result<Vec<_>, _> = p.map(TryInto::try_into).collect();
                InnerAppMacro::Other { name, args: args? }
            }
        }
    };

    Ok(Self{span, inner})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerAppMacro<'a> {
    Msg(Application<'a>),
    Cond(Application<'a>),
    Other {
        name: MacroName<'a>,
        args: Vec<Term<'a>>,
    },
}

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
            return Err(merr(n_op_span, f!("should be {}", operation)))
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

impl<'a> Application<'a> {
    pub fn name(&self) -> &'a str {
        match self {
            Application::ConstVar { content, .. } => *content,
            Application::Application { function, .. } => function.0.content.content,
        }
    }
    pub fn name_span(&self) -> Span<'a> {
        match self {
            Application::ConstVar { span, .. } => *span,
            Application::Application { function, .. } => function.0.span,
        }
    }

    pub fn span(&self) -> Span<'a> {
        match self {
            Application::ConstVar { span, .. } | Application::Application { span, .. } => *span,
        }
    }

    pub fn args(&self) -> VecRef<'_, Term<'a>> {
        match self {
            Application::ConstVar { .. } => VecRef::Empty,
            Application::Application { args, .. } => args.as_slice().into(),
        }
    }
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

impl<'a> DeclareFunction<'a> {
    pub fn name(&self) -> Ident<'a> {
        self.name.0.content
    }

    pub fn args(&'_ self) -> impl Iterator<Item = Ident<'a>> + '_ {
        self.args.args.iter().map(|tn| tn.0.content)
    }

    pub fn out(&self) -> Ident<'a> {
        self.sort.0.content
    }
}

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

impl<'a> Step<'a> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'a str> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
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
        return err(merr(np.as_span(),
            f!("too many arguments (expected at most 5, got {})",
            (6 + p.len()))))
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
    pub fresh_vars: Option<TypedArgument<'a>>,
}
boiler_plate!(Assignement<'a>, 'a, assignement; |p| {
    let span = p.as_span();
    let p = p.into_inner().collect_vec();
    // dest_rule!(span in [cell, term] = p);
    match p.len() {
        2 => {
            as_array!(span in [cell, term] = p);
            Ok(Self {
                span,
                cell: cell.try_into().debug_continue()?,
                term: term.try_into().debug_continue()?,
                fresh_vars: None
            })
        }
        3 => {
            as_array!(span in [vars, cell, term] = p);
            Ok(Self {
                span,
                cell: cell.try_into().debug_continue()?,
                term: term.try_into().debug_continue()?,
                fresh_vars: Some(vars.try_into().debug_continue()?)
            })
        }
        _ => unreachable!()
    }

    // Ok(Self { span, cell, term })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Macro<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub name: MacroName<'a>,
    pub args: TypedArgument<'a>,
    pub term: Term<'a>,
}
boiler_plate!(Macro<'a>, 'a, mlet ; |p| {
    let span = p.as_span();
    dest_rule!(span in [name, args, term] = p);
    Ok(Self {span, name, args, term})
});

impl<'a> Macro<'a> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'a str> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Assert<'a> {
    Assertion(Assertion<'a>),
    Query(Assertion<'a>),
    Lemma(Assertion<'a>),
}
boiler_plate!(l Assert<'a>, 'a, assertion | query | lemma ; |p| {
    assertion_inner => { Ok(Assert::Assertion(p.try_into()?)) }
    query_inner => { Ok(Assert::Query(p.try_into()?)) }
    lemma_inner => { Ok(Assert::Lemma(p.try_into()?)) }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assertion<'a> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Span<'a>,
    pub content: Term<'a>,
}
boiler_plate!(Assertion<'a>, 'a, assertion_inner | query_inner | lemma_inner ; |p| {
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
boiler_plate!(OrderOperation, ordering_operation; {
    order_incompatible => Incompatible,
    order_lt => Lt,
    order_gt => Gt
});

impl<'a, 'b> IntoIterator for &'b TypedArgument<'a> {
    type Item = &'b VariableBinding<'a>;

    type IntoIter = Iter<'b, VariableBinding<'a>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}

pub mod extra {
    use pest::Span;

    use crate::{formula::sort::builtins::STEP, utils::string_ref::StrRef};

    use super::{
        DeclareCell, DeclareFunction, Function, Macro, MacroName, Step, StepName, TypeName,
    };

    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub enum MAsFunction<'a, 'b> {
        // Function(DeclareFunction<'a>),
        Step(&'b Step<'a>),
        Cell(&'b DeclareCell<'a>),
    }

    impl<'a, 'b, 'c> AsFunction<'a, 'b> for &'c MAsFunction<'a, 'b> {
        fn name(self) -> SnN<'a, 'b> {
            match self {
                MAsFunction::Step(s) => s.name(),
                MAsFunction::Cell(c) => c.name(),
            }
        }

        fn args(self) -> Vec<SnN<'a, 'b>> {
            match self {
                MAsFunction::Step(s) => s.args(),
                MAsFunction::Cell(c) => c.args(),
            }
        }

        fn out(self) -> SnN<'a, 'b> {
            match self {
                MAsFunction::Step(s) => s.out(),
                MAsFunction::Cell(c) => c.out(),
            }
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub struct SnN<'a, 'b> {
        pub span: &'b Span<'a>,
        pub name: StrRef<'a>,
    }

    impl<'a, 'b> From<&'b TypeName<'a>> for SnN<'a, 'b> {
        fn from(value: &'b TypeName<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content.into(),
            }
        }
    }

    impl<'a, 'b> From<&'b Function<'a>> for SnN<'a, 'b> {
        fn from(value: &'b Function<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content.into(),
            }
        }
    }

    impl<'a, 'b> From<&'b StepName<'a>> for SnN<'a, 'b> {
        fn from(value: &'b StepName<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content.into(),
            }
        }
    }

    impl<'a, 'b> From<&'b MacroName<'a>> for SnN<'a, 'b> {
        fn from(value: &'b MacroName<'a>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.0.content.content.into(),
            }
        }
    }

    pub trait AsFunction<'a, 'b> {
        fn name(self) -> SnN<'a, 'b>;
        fn args(self) -> Vec<SnN<'a, 'b>>;
        fn out(self) -> SnN<'a, 'b>;
    }

    impl<'a, 'b> AsFunction<'a, 'b> for &'b DeclareFunction<'a> {
        fn name(self) -> SnN<'a, 'b> {
            From::from(&self.name)
        }

        fn args(self) -> Vec<SnN<'a, 'b>> {
            self.args.args.iter().map(|tn| tn.into()).collect()
        }

        fn out(self) -> SnN<'a, 'b> {
            From::from(&self.sort)
        }
    }

    impl<'a, 'b> AsFunction<'a, 'b> for &'b DeclareCell<'a> {
        fn name(self) -> SnN<'a, 'b> {
            From::from(&self.name)
        }

        fn args(self) -> Vec<SnN<'a, 'b>> {
            self.args
                .args
                .iter()
                .map(|tn| tn.into())
                // .chain([SnN {
                //     span: &self.span,
                //     name: STEP.name(),
                // }])
                .collect()
        }

        fn out(self) -> SnN<'a, 'b> {
            From::from(&self.sort)
        }
    }

    impl<'a, 'b> AsFunction<'a, 'b> for &'b Step<'a> {
        fn name(self) -> SnN<'a, 'b> {
            From::from(&self.name)
        }

        fn args(self) -> Vec<SnN<'a, 'b>> {
            self.args
                .bindings
                .iter()
                .map(|b| From::from(&b.type_name))
                .collect()
        }

        fn out(self) -> SnN<'a, 'b> {
            SnN {
                span: &self.span,
                name: STEP.name(),
            }
        }
    }

    impl<'a, 'b> AsFunction<'a, 'b> for &'b Macro<'a> {
        fn name(self) -> SnN<'a, 'b> {
            From::from(&self.name)
        }

        fn args(self) -> Vec<SnN<'a, 'b>> {
            self.args
                .bindings
                .iter()
                .map(|b| From::from(&b.type_name))
                .collect()
        }

        fn out(self) -> SnN<'a, 'b> {
            panic!()
        }
    }
}
