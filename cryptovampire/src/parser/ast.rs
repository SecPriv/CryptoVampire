use std::{
    fmt::Display,
    slice::{self, Iter},
    sync::Arc,
};

use derivative::Derivative;
use itertools::{chain, Itertools};
use log::trace;
use pest::{iterators::Pair, Parser, Position};

use cryptovampire_lib::{
    formula::function::{
        builtin,
        inner::term_algebra::{self},
    },
    INIT_STEP_NAME,
};
use utils::{destvec, implvec, match_as_trait, vecref::VecRef};

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
                let str = $p.as_str();
                trace!("parsing {str}");
                debug_rule!($p, $($rule)|+);

                let r = {$content};
                trace!("successfully parsed {str}");
                r
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

/// The default init step when it's not defined. This is a function because
/// it needs to be generic.
///
/// See [HasInitStep::ref_init_step_ast] a degenericied version
#[allow(non_snake_case)]
pub fn INIT_STEP_AST<S>() -> Step<'static, S>
where
    S: From<&'static str>,
{
    let condition = Term::new_default_const(term_algebra::connective::TRUE_NAME.into());
    let message = Term::new_default_const(builtin::EMPTY_FUN_NAME.into());

    Step {
        span: Location::default(),
        name: StepName::from_s(INIT_STEP_NAME.into()),
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

impl<'s, T> From<T> for Sub<'s, T> {
    fn from(c: T) -> Self {
        Self::from_content(c)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AST<'a, S = &'a str> {
    Declaration(Arc<Declaration<'a, S>>),
    Step(Arc<Step<'a, S>>),
    Order(Arc<Order<'a, S>>),
    AssertCrypto(Arc<AssertCrypto<'a, S>>),
    Assert(Arc<Assert<'a, S>>),
    Let(Arc<Macro<'a, S>>),
}
boiler_plate!(l AST<'a>, 'a, content; |p| {
    declaration => { Ok(AST::Declaration(Arc::new(p.try_into()?))) }
    step => { Ok(AST::Step(Arc::new(p.try_into()?))) }
    order => { Ok(AST::Order(Arc::new(p.try_into()?))) }
    assertion_crypto => { Ok(AST::AssertCrypto(Arc::new(p.try_into()?))) }
    assertion | query | lemma => { Ok(AST::Assert(Arc::new(p.try_into()?))) }
    mlet => { Ok(AST::Let(Arc::new(p.try_into()?))) }
});

impl<'a, S: Display> Display for AST<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(Self, |x| in self => Declaration | Step | Order | AssertCrypto | Assert | Let
            {writeln!(f, "{x}")})
    }
}

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

impl<'a, S: Display> Display for Ident<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for Ident<'a, S> {
    fn from(value: S) -> Self {
        Self::from_content(value)
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
impl<'a, S: Display> Display for TypeName<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for TypeName<'a, S> {
    fn from(value: S) -> Self {
        TypeName(Sub::from(Ident::from(value)))
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

impl<'a, S: Display> Display for MacroName<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for MacroName<'a, S> {
    fn from(value: S) -> Self {
        MacroName(Sub::from(Ident::from(value)))
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

impl<'a, S: Display> Display for Function<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
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

impl<'a, S: Display> Display for Variable<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for Variable<'a, S> {
    fn from(value: S) -> Self {
        Variable(value.into())
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

    pub fn from_s(s: S) -> Self {
        Self(Sub {
            span: Default::default(),
            content: Ident::from_content(s),
        })
    }
}

impl<'a, S: Display> Display for StepName<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for StepName<'a, S> {
    fn from(value: S) -> Self {
        StepName(Ident::from_content(value).into())
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

impl<'a, S: Display> Display for TypedArgument<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.bindings.iter().format(", "))
    }
}

impl<'a, S, U> FromIterator<U> for TypedArgument<'a, S>
where
    VariableBinding<'a, S>: From<U>,
{
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let bindings = iter.into_iter().map_into().collect();
        Self {
            span: Default::default(),
            bindings,
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

impl<'a, S: Display> Display for VariableBinding<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", &self.variable, &self.type_name)
    }
}

impl<'a, S, V, T> From<(V, T)> for VariableBinding<'a, S>
where
    Variable<'a, S>: From<V>,
    TypeName<'a, S>: From<T>,
{
    fn from((variable, type_name): (V, T)) -> Self {
        let variable = variable.into();
        let type_name = type_name.into();
        Self {
            span: Default::default(),
            variable,
            type_name,
        }
    }
}

// -----------------------------------------------------------------------------
// ---------------------------------- terms ------------------------------------
// -----------------------------------------------------------------------------

mod term;
pub use term::{InnerTerm, Term};

pub use mmacro::*;
mod mmacro;

pub use infix::*;
mod infix;

pub use application::*;
mod application;

pub use if_then_else::*;
mod if_then_else;

pub use find_such_that::*;
mod find_such_that;

pub use quantifier::*;
mod quantifier;

pub use let_in::*;
mod let_in;

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

impl<'a, S: Display> Display for Declaration<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(ast::Declaration, |x| in self => Type | Function | Cell
                    {x.fmt(f)})
    }
}

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

impl<'a, S: Display> Display for DeclareType<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, options, .. } = self;
        write!(f, "type {name} {options}")
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

impl<'a, S: Display> Display for DeclareFunction<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            sort,
            options,
            ..
        } = self;
        write!(f, "fun {name}{args}:{sort} {options}")
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

impl<'a, S: Display> Display for DeclareFunctionArgs<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            Ok(())
        } else {
            write!(f, "({})", self.args.iter().format(", "))
        }
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Function<'a, S>,
    pub args: DeclareFunctionArgs<'a, S>,
    pub sort: TypeName<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(DeclareCell<'a>, 'a, declare_cell; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
});

impl<'a, S: Display> Display for DeclareCell<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            sort,
            options,
            ..
        } = self;
        write!(f, "cell {name}{args}:{sort} {options}")
    }
}
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

impl<'a, S: Display> Display for Step<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            condition,
            message,
            assignements,
            options,
            ..
        } = self;
        write!(f, "step {name}{args}\n\t{{{condition}}}\n\t{{{message}}}")?;
        if let Some(a) = assignements {
            write!(f, "\n\t{a}")?;
        }
        write!(f, "\n{options}")
    }
}

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

impl<'a, S: Display> Display for Assignements<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.assignements.iter().format(", "))
    }
}

impl<'a, S> FromIterator<Assignement<'a, S>> for Assignements<'a, S> {
    fn from_iter<T: IntoIterator<Item = Assignement<'a, S>>>(iter: T) -> Self {
        Self {
            span: Default::default(),
            assignements: iter.into_iter().collect(),
        }
    }
}

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

impl<'a, S: Display> Display for Assignement<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            cell,
            term,
            fresh_vars,
            ..
        } = self;
        if let Some(fv) = fresh_vars {
            write!(f, "{fv} ")?;
        }
        write!(f, "{cell} <- {term}")
    }
}

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

impl<'a, S: Display> Display for Macro<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            term,
            options,
            ..
        } = self;
        write!(f, "let {name}{args} = {term} {options}")
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

impl<'a, S: Display> Display for Options<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.options.iter().format(", "))
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

impl<'a, S: Display> Display for MOption<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
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

impl<'a, S: Display> Display for Assert<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Assert::Assertion(a) => write!(f, "assert {a}"),
            Assert::Query(a) => write!(f, "query {a}"),
            Assert::Lemma(a) => write!(f, "lemma {a}"),
        }
    }
}

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

impl<'a, S: Display> Display for Assertion<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            content, options, ..
        } = self;
        write!(f, "{content} {options}")
    }
}

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
impl<'a, S: Display> Display for AssertCrypto<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            functions,
            options,
            ..
        } = self;
        write!(
            f,
            "assert-crypto {name} {} {options}",
            functions.iter().format(", ")
        )
    }
}

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
    pub guard: Option<Term<'a, S>>,
}
boiler_plate!(Order<'a>, 'a, order ; |p| {
    let span = p.as_span().into();
    let mut p = p.into_inner();
    let quantifier = p.next().unwrap().try_into()?;
    let args = p.next().unwrap().try_into()?;
    let (guard, nxt) = {
        let n = p.next().unwrap();
        match n.as_rule() {
            Rule::order_guard => {
                let guard = n.into_inner().next()
                                .unwrap().try_into()?;
                (Some(guard), p.next().unwrap())
            }
            _ => (None, n)
        }
    };
    let t1 = nxt.try_into()?;
    let kind = p.next().unwrap().try_into()?;
    let t2 = p.next().unwrap().try_into()?;
    let options = p.next().map(|r| r.try_into().debug_continue())
                    .transpose()?.unwrap_or(Options::empty(span));
    if let Some(_) = p.next() {
        bail_at!(&span, "too many arguments")
    }

    Ok(Self {span, quantifier, args, t1, t2, kind, options, guard})
});

impl<'a, S: Display> Display for Order<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            quantifier,
            args,
            t1,
            t2,
            kind,
            options,
            ..
        } = self;
        write!(f, "order {quantifier}{args}{{{t1} {kind} {t2}}} {options}")
    }
}

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
impl Display for OrderOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let op = match self {
            OrderOperation::Incompatible => "<>",
            OrderOperation::Lt => "<",
            OrderOperation::Gt => ">",
        };
        write!(f, "{op}")
    }
}

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
