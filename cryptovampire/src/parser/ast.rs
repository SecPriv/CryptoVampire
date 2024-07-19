use std::{
    fmt::Display,
    slice::{self, Iter},
};

use derivative::Derivative;
use if_chain::if_chain;
use itertools::{chain, Itertools};
use log::trace;
use pest::{iterators::Pair, Parser, Position};

use cryptovampire_lib::INIT_STEP_NAME;
use utils::{destvec, vecref::VecRef};

use super::*;
use crate::bail_at;

macro_rules! unreachable_rules {
    ($span:expr, $urule:expr; $($rule:ident),* ) => {
        $span.wrong_rule(vec![$(Rule::$rule),+], vec![$urule])?
    };
}

macro_rules! debug_rule {
    ($p:ident, $($rule:ident)|+) => {
        if cfg!(debug_assertions) && match $p.as_rule() {
                $(Rule::$rule)|+ => false,
                _ => true
            }
        {
            unreachable_rules!($crate::parser::Location::from($p.as_span()),  $p.as_rule(); $($rule),*);
        }
    };
}

macro_rules! boiler_plate {
    ($t:ty, $lt:lifetime, $($rule:ident)|+; |$p:ident| $content:block) => {
        impl<$lt> TryFrom<Pair<$lt, Rule>> for $t {
            type Error = $crate::parser::InputError;

            fn try_from($p: Pair<$lt, Rule>) -> std::result::Result<$t, Self::Error> {
                debug_rule!($p, $($rule)|+);

                $content
            }
        }
    };

    (l $t:ty, $lt:lifetime, $($rule:ident)|+; |$p:ident| { $($($pat:ident)|+ => $content:block)* }) => {
        boiler_plate!($t, 'a, $($rule)|+; |p| {
            let span : Location<'a> = p.as_span().into();
            let mut p_iter = p.into_inner();
            let $p = p_iter.next().unwrap();

            if let Some(p) = p_iter.next() {
                bail_at!(&p, "too much")
                // return err(merr(p.as_span().into(), f!("too much")))
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
            bail_at!(&$span, "{}", err)
        }}
    };

    ($span:ident in [$($arg:ident),*,..$leftover:ident] = $vec:expr) => {
        destvec!{ [$($arg),*,..$leftover] = $vec; |err| {
            // return Err(merr($span, f!("{}", err)))
            bail_at!(&$span, "{}", err)
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

macro_rules! destruct_rule {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        as_array!($span in [$($arg),*] = macro_helper::AsInner::m_into_inner($vec));
        $(
            let $arg = $arg.try_into().debug_continue()?;
        )*
    };

    ($span:ident in [$($arg:ident),*, ?$option:ident] = $vec:expr) => {
        as_array!($span in [$($arg),*,..leftover] = macro_helper::AsInner::m_into_inner($vec));
        $(
            let $arg = $arg.try_into().debug_continue()?;
        )*
        let $option = leftover.next().map(|r| r.try_into().debug_continue()).transpose()?.unwrap_or(Options::empty($span));
        if let Some(_) = leftover.next() {
            bail_at!(&$span, "too many arguments")
            // return Err(merr($span, f!("too many arguments")))
        }
    }
}

// const INIT_STEP_STRING: &'static str = concatcp!("step ", INIT_STEP_NAME, "(){true}{empty}");

pub fn INIT_STEP_AST<S>() -> Step<'static, S>
where
    S: From<&'static str>,
{
    let condition = Term::new_default_const("true".into());
    let message = Term::new_default_const("empty".into());

    Step {
        span: Location::default(),
        name: StepName::from_S(INIT_STEP_NAME.into()),
        args: TypedArgument::default(),
        condition,
        message,
        assignements: Default::default(),
        options: Default::default(),
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ASTList<'str, S = &'str str> {
    pub content: Vec<AST<'str, S>>,
    pub begining: Option<Position<'str>>,
}

impl<'str, S> ASTList<'str, S> {
    pub fn shorten_ref<'a>(&'a self) -> &'a ASTList<'a, S> {
        self
    }
}

impl<'a> TryFrom<&'a str> for ASTList<'a, &'a str> {
    type Error = InputError;

    fn try_from(value: &'a str) -> MResult<Self> {
        let mut pairs = MainParser::parse(Rule::file, value).debug_continue()?;

        Ok(ASTList {
            content: pairs
                .next()
                .unwrap()
                .into_inner()
                .filter(|p| p.as_rule() == Rule::content)
                .map(|p| {
                    trace!(" --> {}", p.as_str());
                    p.try_into().debug_continue()
                })
                .try_collect()
                .debug_continue()?,
            begining: Some(Position::from_start(value)),
        })
    }
}

impl<'str, 'b, S> IntoIterator for &'b ASTList<'str, S> {
    type Item = &'b AST<'str, S>;

    type IntoIter = Iter<'b, AST<'str, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.content.iter()
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Sub<'s, T> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'s>,
    pub content: T,
}

impl<'s, T> Sub<'s, T> {
    /// using [Location::default]
    pub fn from_content(c: T) -> Self {
        Self {
            span: Default::default(),
            content: c,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AST<'a, S = &'a str> {
    Declaration(Box<Declaration<'a, S>>),
    Step(Box<Step<'a, S>>),
    Order(Box<Order<'a, S>>),
    AssertCrypto(Box<AssertCrypto<'a, S>>),
    Assert(Box<Assert<'a, S>>),
    Let(Box<Macro<'a, S>>),
}
boiler_plate!(l AST<'a>, 'a, content; |p| {
    declaration => { Ok(AST::Declaration(Box::new(p.try_into()?))) }
    step => { Ok(AST::Step(Box::new(p.try_into()?))) }
    order => { Ok(AST::Order(Box::new(p.try_into()?))) }
    assertion_crypto => { Ok(AST::AssertCrypto(Box::new(p.try_into()?))) }
    assertion | query | lemma => { Ok(AST::Assert(Box::new(p.try_into()?))) }
    mlet => { Ok(AST::Let(Box::new(p.try_into()?))) }
});

/// [Rule::ident]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Ident<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub content: S,
}
boiler_plate!(Ident<'s>, 's, ident; |p| {
    Ok(Ident { span: p.as_span().into(), content: p.as_str()})
});

impl<'s, S> Ident<'s, S> {
    pub fn name(&self) -> &S {
        &self.content
    }

    /// using [Location::default]
    pub fn from_content(s: S) -> Self {
        Ident {
            span: Default::default(),
            content: s,
        }
    }
}

/// [Rule::type_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeName<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(TypeName<'a>, 'a, type_name; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> TypeName<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn name_span(&self) -> Location<'a> {
        self.0.span
    }
}

/// [Rule::macro_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MacroName<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(MacroName<'a>, 'a, macro_name; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> MacroName<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> Location<'a> {
        self.0.span
    }
}

/// [Rule::function]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Function<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(Function<'a>, 'a, function; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> Function<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> Location<'a> {
        self.0.span
    }

    pub fn from_name(s: S) -> Self {
        Self(Sub::from_content(Ident::from_content(s)))
    }
}

/// [Rule::variable]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable<'a, S = &'a str>(pub Sub<'a, S>);
boiler_plate!(Variable<'a>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.as_str() }))
});

impl<'a, S> Variable<'a, S> {
    pub fn name(&self) -> &S {
        &self.0.content
    }
}

/// [Rule::step_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct StepName<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(StepName<'a>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> StepName<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn from_S(s: S) -> Self {
        Self(Sub {
            span: Default::default(),
            content: Ident::from_content(s),
        })
    }
}

// operation in `Infix`

/// [Rule::typed_arguments]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypedArgument<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub bindings: Vec<VariableBinding<'a, S>>,
}
boiler_plate!(TypedArgument<'a>, 'a, typed_arguments; |p| {
    let span = p.as_span().into();
    let bindings : Result<Vec<_>, _> = p.into_inner().map(TryInto::try_into).collect();
    Ok(TypedArgument { span, bindings: bindings? })
});

impl<'a, S> Default for TypedArgument<'a, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            bindings: Default::default(),
        }
    }
}

/// [Rule::variable_binding]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VariableBinding<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub variable: Variable<'a, S>,
    pub type_name: TypeName<'a, S>,
}
boiler_plate!(VariableBinding<'s>, 's, variable_binding; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [variable, type_name] = p.into_inner());
    Ok(VariableBinding{span, variable, type_name})
});

// -----------------------------------------------------------------------------
// ---------------------------------- terms ------------------------------------
// -----------------------------------------------------------------------------

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Term<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub inner: InnerTerm<'a, S>,
}
boiler_plate!(Term<'s>, 's, term; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [inner] = p.into_inner());
    Ok(Term{span, inner})
});

impl<'a, S> Term<'a, S> {
    /// build a new constant term, relying on the implementation of [Location::default]
    pub fn new_default_const(s: S) -> Self {
        Term {
            span: Default::default(),
            inner: InnerTerm::Application(Box::new(Application::Application {
                span: Default::default(),
                function: Function::from_name(s),
                args: Default::default(),
            })),
        }
    }
}

/// Gather many rules at once, namely:
/// - [Rule::infix_term]
/// - [Rule::commun_base]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum InnerTerm<'a, S = &'a str> {
    LetIn(Box<LetIn<'a, S>>),
    If(Box<IfThenElse<'a, S>>),
    Fndst(Box<FindSuchThat<'a, S>>),
    Quant(Box<Quantifier<'a, S>>),
    Application(Box<Application<'a, S>>),
    Infix(Box<Infix<'a, S>>),
    Macro(Box<AppMacro<'a, S>>),
}
boiler_plate!(InnerTerm<'s>, 's, inner_term; |p| {
    let span: Location = p.as_span().into();
    as_array!(span in [nxt] = p.into_inner());
    match nxt.as_rule() {
        Rule::infix_term => {
            Ok(InnerTerm::Infix(Box::new(nxt.try_into()?)))
        }
        Rule::commun_base => {
            as_array!(span in [cmn_rule] = nxt.into_inner());
            match cmn_rule.as_rule(){
                Rule::let_in => {
                    Ok(InnerTerm::LetIn(Box::new(cmn_rule.try_into()?)))
                },
                Rule::if_then_else => {
                    Ok(InnerTerm::If(Box::new(cmn_rule.try_into()?)))
                },
                Rule::find_such_that => {
                    Ok(InnerTerm::Fndst(Box::new(cmn_rule.try_into()?)))
                },
                Rule::quantifier => {
                    Ok(InnerTerm::Quant(Box::new(cmn_rule.try_into()?)))
                },
                Rule::application => {
                    Ok(InnerTerm::Application(Box::new(cmn_rule.try_into()?)))
                },
                Rule::macro_application => {
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
pub struct AppMacro<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub inner: InnerAppMacro<'a, S>,
}

fn from_term_to_application<'a>(p: Pair<'a, Rule>) -> MResult<Application<'a>> {
    debug_rule!(p, term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, inner_term);
    let p = p.into_inner().next().unwrap();
    debug_rule!(p, commun_base);
    let p = p.into_inner().next().unwrap();
    p.try_into()
}

boiler_plate!(AppMacro<'a>, 'a, macro_application; |p| {
    let span = p.as_span().into();
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
pub enum InnerAppMacro<'a, S = &'a str> {
    Msg(Application<'a, S>),
    Cond(Application<'a, S>),
    Other {
        name: MacroName<'a, S>,
        args: Vec<Term<'a, S>>,
    },
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Infix<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub operation: Operation,
    pub terms: Vec<Term<'a, S>>,
}
boiler_plate!(Infix<'a>, 'a, infix_term; |p| {
    let span = p.as_span().into();
    let mut terms = Vec::new();

    let mut p = p.into_inner();

    terms.push(p.next().unwrap().try_into()?);
    let operation : Operation = p.next().unwrap().try_into()?;
    terms.push(p.next().unwrap().try_into()?);

    while let Some(n_op) = p.next() {
        let n_op_span = n_op.as_span();
        if_chain!{
            if let Ok(tmp) = Operation::try_from(n_op);
            if tmp == operation;
            then {
                bail_at!(n_op_span, "should be {}", operation)
            }
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
pub enum Application<'a, S = &'a str> {
    ConstVar {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        span: Location<'a>,
        content: S,
    },
    Application {
        #[derivative(PartialOrd = "ignore", Ord = "ignore")]
        span: Location<'a>,
        function: Function<'a, S>,
        args: Vec<Term<'a, S>>,
    },
}

impl<'a, S> Application<'a, S> {
    pub fn name(&self) -> &S {
        match self {
            Application::ConstVar { content, .. } => content,
            Application::Application { function, .. } => function.name(),
        }
    }

    pub fn args(&self) -> VecRef<'_, Term<'a, S>> {
        match self {
            Application::ConstVar { .. } => VecRef::Empty,
            Application::Application { args, .. } => args.as_slice().into(),
        }
    }
    // }
    // impl<'a> Application<'a> {
    pub fn name_span(&self) -> Location<'a> {
        match self {
            Application::ConstVar { span, .. } => *span,
            Application::Application { function, .. } => function.0.span,
        }
    }

    pub fn span(&self) -> Location<'a> {
        match self {
            Application::ConstVar { span, .. } | Application::Application { span, .. } => *span,
        }
    }
}
boiler_plate!(Application<'a>, 'a, application; |p| {
    let span = p.as_span().into();
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
pub struct IfThenElse<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub condition: Term<'a, S>,
    pub left: Term<'a, S>,
    pub right: Term<'a, S>,
}
boiler_plate!(IfThenElse<'a>, 'a, if_then_else; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [condition, left, right] = p.into_inner());
    Ok(IfThenElse { span, condition, left, right})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FindSuchThat<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub vars: TypedArgument<'a, S>,
    pub condition: Term<'a, S>,
    pub left: Term<'a, S>,
    pub right: Term<'a, S>,
}
boiler_plate!(FindSuchThat<'a>, 'a, find_such_that; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [vars, condition, left, right] = p.into_inner());
    Ok(Self { vars, span, condition, left, right})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'a, S = &'a str> {
    pub kind: QuantifierKind,
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub vars: TypedArgument<'a, S>,
    pub content: Term<'a, S>,
}
boiler_plate!(Quantifier<'a>, 'a, quantifier; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [kind, vars, content] = p.into_inner());
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
pub struct LetIn<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub var: Variable<'a, S>,
    pub t1: Term<'a, S>,
    pub t2: Term<'a, S>,
}
boiler_plate!(LetIn<'a>, 'a, let_in; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [var, t1, t2] = p.into_inner());
    Ok(Self { span, var, t1, t2})
});

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Declaration<'a, S = &'a str> {
    Type(DeclareType<'a, S>),
    Function(DeclareFunction<'a, S>),
    Cell(DeclareCell<'a, S>),
}
boiler_plate!(l Declaration<'a>, 'a, declaration; |p| {
    declare_type => { Ok(Declaration::Type(p.try_into()?)) }
    declare_function => { Ok(Declaration::Function(p.try_into()?)) }
    declare_cell => { Ok(Declaration::Cell(p.try_into()?)) }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareType<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: TypeName<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(DeclareType<'a>, 'a, declare_type; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, ?options] = p);
    Ok(Self { span, name, options })
});

impl<'a, S> DeclareType<'a, S> {
    pub fn name(&self) -> &S {
        self.name.name()
    }

    pub fn name_span(&self) -> &Location<'a> {
        &self.name.0.span
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunction<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Function<'a, S>,
    pub args: DeclareFunctionArgs<'a, S>,
    pub sort: TypeName<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(DeclareFunction<'a>, 'a, declare_function; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
});

impl<'a, S> DeclareFunction<'a, S> {
    pub fn name(&self) -> &Ident<'a, S> {
        &self.name.0.content
    }

    pub fn args(&'_ self) -> impl Iterator<Item = &'_ Ident<'a, S>> + '_ {
        self.args.args.iter().map(|tn| &tn.0.content)
    }

    pub fn out(&self) -> &Ident<'a, S> {
        &self.sort.0.content
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunctionArgs<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub args: Vec<TypeName<'a, S>>,
}
boiler_plate!(DeclareFunctionArgs<'a>, 'a, declare_function_args; |p| {
    let span = p.as_span().into();
    let args = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, args })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Function<'a, S>,
    pub args: DeclareFunctionArgs<'a, S>,
    pub sort: TypeName<'a, S>,
}
boiler_plate!(DeclareCell<'a>, 'a, declare_cell; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, sort] = p);
    Ok(Self { span, name, args, sort })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Step<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: StepName<'a, S>,
    pub args: TypedArgument<'a, S>,
    pub condition: Term<'a, S>,
    pub message: Term<'a, S>,
    pub assignements: Option<Assignements<'a, S>>,
    pub options: Options<'a, S>,
}

impl<'a, S> Step<'a, S> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'_ S> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}
boiler_plate!(Step<'a>, 'a, step; |p| {
    let span = p.as_span().into();
    // dest_rule!(span in [name, args, condition, message, assignements] = p);
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let args = p.next().unwrap().try_into()?;
    let condition = p.next().unwrap().try_into()?;
    let message = p.next().unwrap().try_into()?;

    // temporary save the Rule obj
    let assignement_rule = p.next();
    let options_rule = p.next();

    // replace it by the right object
    let assignements = assignement_rule.clone().map(TryInto::try_into).transpose()?;
    let options = {
        // if assignement is not a [Assignements<'a>] then either it is an [Options<'a>]
        // or the parsing should fail anyway
        let rule = if assignements.is_none() { assignement_rule } else { options_rule };
        rule.map(TryInto::try_into).transpose()?
    }.unwrap_or(Options::empty(span));

    if let Some(np) = p.next() { // whatever happens, there shouldn't be anything left
        bail_at!(&np, "too many arguments (expected at most 6, got {})", (7 + p.len()))
    }

    Ok(Self { span, name, args, condition, message, assignements, options})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignements<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub assignements: Vec<Assignement<'a, S>>,
}
boiler_plate!(Assignements<'a>, 'a, assignements; |p| {
    let span = p.as_span().into();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, assignements })
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub cell: Application<'a, S>,
    pub term: Term<'a, S>,
    pub fresh_vars: Option<TypedArgument<'a, S>>,
}
boiler_plate!(Assignement<'a>, 'a, assignement; |p| {
    let span = p.as_span().into();
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
pub struct Macro<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: MacroName<'a, S>,
    pub args: TypedArgument<'a, S>,
    pub term: Term<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(Macro<'a>, 'a, mlet ; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, term, ?options] = p);
    Ok(Self {span, name, args, term, options})
});

impl<'a, S> Macro<'a, S> {
    pub fn args_names(&'_ self) -> impl Iterator<Item = &'_ S> + '_ {
        self.args.bindings.iter().map(|vb| vb.variable.name())
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Options<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub options: Vec<MOption<'a, S>>,
}

impl<'a, S> Default for Options<'a, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            options: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MOption<'a, S = &'a str>(Ident<'a, S>);

impl<'a, S> From<Ident<'a, S>> for MOption<'a, S> {
    fn from(value: Ident<'a, S>) -> Self {
        Self(value)
    }
}

boiler_plate!(Options<'a>, 'a, options; |p| {
    let span = p.as_span().into();
    let options = p.into_inner().map(Ident::try_from).map(|r| r.map(MOption::from)).try_collect()?;
    Ok(Self { span, options })
});
impl<'a, S> Options<'a, S> {
    pub fn empty(span: Location<'a>) -> Self {
        Self {
            span,
            options: Default::default(),
        }
    }

    pub fn as_str_list<'b>(&'b self) -> impl Iterator<Item = &'_ S> + 'b {
        self.options.iter().map(|MOption(i)| &i.content)
    }

    pub fn iter<'b>(&'b self) -> <&'b Self as IntoIterator>::IntoIter {
        (&self).into_iter()
    }
    pub fn contains(&self, str: &str) -> bool
    where
        S: Borrow<str>,
    {
        self.as_str_list().any(|s| s.borrow() == str)
    }
}

impl<'a, 'b, S> IntoIterator for &'b Options<'a, S> {
    type Item = &'b MOption<'a, S>;

    type IntoIter = slice::Iter<'b, MOption<'a, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.options.iter()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Assert<'a, S = &'a str> {
    Assertion(Assertion<'a, S>),
    Query(Assertion<'a, S>),
    Lemma(Assertion<'a, S>),
}
boiler_plate!(l Assert<'a>, 'a, assertion | query | lemma ; |p| {
    assertion_inner => { Ok(Assert::Assertion(p.try_into()?)) }
    query_inner => { Ok(Assert::Query(p.try_into()?)) }
    lemma_inner => { Ok(Assert::Lemma(p.try_into()?)) }
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assertion<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub content: Term<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(Assertion<'a>, 'a, assertion_inner | query_inner | lemma_inner ; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [content, ?options] = p);
    Ok(Self {span, content, options})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct AssertCrypto<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Ident<'a, S>,
    pub functions: Vec<Function<'a, S>>,
    pub options: Options<'a, S>,
}
boiler_plate!(AssertCrypto<'a>, 'a, assertion_crypto ; |p| {
    let span = p.as_span().into();
    let mut p = p.into_inner();
    let name = p.next().unwrap().try_into()?;
    let mut p = p.collect_vec();
    // try to parse the option, if it fails, it means there weren't any
    let mut options  = Options::empty(span);
    let mut extra_fun = None;

    if let Some(r) = p.pop() {
        if let Rule::options = r.as_rule() {
            options = r.try_into()?;
        } else {
            extra_fun = Some(r)
        }
    }

    let functions = chain!(p.into_iter(), extra_fun).map(TryInto::try_into).try_collect()?;

    Ok(Self {span, name, functions, options})
});

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Order<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub quantifier: QuantifierKind,
    pub args: TypedArgument<'a, S>,
    pub t1: Term<'a, S>,
    pub t2: Term<'a, S>,
    pub kind: OrderOperation,
    pub options: Options<'a, S>,
}
boiler_plate!(Order<'a>, 'a, order ; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [quantifier, args, t1, kind, t2, ?options] = p);
    Ok(Self {span, quantifier, args, t1, t2, kind, options})
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

impl<'a, 'b, S> IntoIterator for &'b TypedArgument<'a, S> {
    type Item = &'b VariableBinding<'a, S>;

    type IntoIter = Iter<'b, VariableBinding<'a, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}

pub mod extra {

    use cryptovampire_lib::formula::sort::builtins::STEP;
    use utils::string_ref::StrRef;

    use super::{
        error::Location, DeclareCell, DeclareFunction, Function, Macro, MacroName, Step, StepName,
        TypeName,
    };

    /// Span and Name
    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub struct SnN<'a, 'b> {
        pub span: &'b Location<'a>,
        pub name: StrRef<'a>,
    }

    impl<'a, 'b, S> From<&'b TypeName<'a, S>> for SnN<'a, 'b>
    where
        StrRef<'a>: From<&'b S>,
    {
        fn from(value: &'b TypeName<'a, S>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.name().into(),
            }
        }
    }

    impl<'a, 'b, S> From<&'b Function<'a, S>> for SnN<'a, 'b>
    where
        StrRef<'a>: From<&'b S>,
    {
        fn from(value: &'b Function<'a, S>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.name().into(),
            }
        }
    }

    impl<'a, 'b, S> From<&'b StepName<'a, S>> for SnN<'a, 'b>
    where
        StrRef<'a>: From<&'b S>,
    {
        fn from(value: &'b StepName<'a, S>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.name().into(),
            }
        }
    }

    impl<'a, 'b, S> From<&'b MacroName<'a, S>> for SnN<'a, 'b>
    where
        StrRef<'a>: From<&'b S>,
    {
        fn from(value: &'b MacroName<'a, S>) -> Self {
            SnN {
                span: &value.0.span,
                name: value.name().into(),
            }
        }
    }

    pub trait AsFunction<'a, 'b> {
        fn name(self) -> SnN<'a, 'b>;
        fn args(self) -> Vec<SnN<'a, 'b>>;
        #[allow(dead_code)]
        fn out(self) -> SnN<'a, 'b>;
    }

    impl<'a, 'b, S> AsFunction<'a, 'b> for &'b DeclareFunction<'a, S>
    where
        StrRef<'a>: From<&'b S>,
    {
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

    impl<'a, 'b, S> AsFunction<'a, 'b> for &'b DeclareCell<'a, S>
    where
        StrRef<'a>: From<&'b S>,
    {
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

    impl<'a, 'b, S> AsFunction<'a, 'b> for &'b Step<'a, S>
    where
        StrRef<'a>: From<&'b S>,
    {
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

    impl<'a, 'b, S> AsFunction<'a, 'b> for &'b Macro<'a, S>
    where
        StrRef<'a>: From<&'b S>,
    {
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
