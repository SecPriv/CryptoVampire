use std::ops::{BitAnd, BitOr, Not, Shr};

use location::ASTLocation;
use term_algebra::connective::NOT_NAME;

use super::*;
use crate::formula::utils::Applicable;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Term<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: ASTLocation<'str>,
    pub inner: InnerTerm<'str, S>,
}

boiler_plate!(Term<'s, &'s str>, 's, term; |p| {
    let span = p.as_span();
    destruct_rule!(span in [inner] = p.into_inner());
    Ok(Term{span: span.into(), inner})
});

impl<'str, S> Term<'str, S> {
    /// build a new constant term, relying on the implementation of [Location::default]
    pub fn new_default_const(s: S) -> Self {
        Term {
            span: Default::default(),
            inner: InnerTerm::Application(Arc::new(Application::Application {
                span: Default::default(),
                function: Function::from_name(s),
                args: Default::default(),
            })),
        }
    }
}

impl<'str, S: Display> Display for Term<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

macro_rules! from_i_term {
    ($v:ident, $t:ident) => {
        impl<'str, S> From<$t<'str, S>> for Term<'str, S> {
            fn from(value: $t<'str, S>) -> Self {
                Term {
                    span: value.span.clone(),
                    inner: InnerTerm::$v(Arc::new(value)),
                }
            }
        }
    };
}

from_i_term!(LetIn, LetIn);
from_i_term!(If, IfThenElse);
from_i_term!(Fndst, FindSuchThat);
from_i_term!(Quant, Quantifier);
from_i_term!(Infix, Infix);
from_i_term!(Macro, AppMacro);
impl<'str, S> From<Application<'str, S>> for Term<'str, S> {
    fn from(value: Application<'str, S>) -> Self {
        Term {
            span: value.span().clone(),
            inner: InnerTerm::Application(Arc::new(value)),
        }
    }
}

/// Gather many rules at once, namely:
/// - [Rule::infix_term]
/// - [Rule::commun_base]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum InnerTerm<'str, S> {
    LetIn(Arc<LetIn<'str, S>>),
    If(Arc<IfThenElse<'str, S>>),
    Fndst(Arc<FindSuchThat<'str, S>>),
    Quant(Arc<Quantifier<'str, S>>),
    Application(Arc<Application<'str, S>>),
    Infix(Arc<Infix<'str, S>>),
    Macro(Arc<AppMacro<'str, S>>),
}

boiler_plate!(InnerTerm<'s, &'s str>, 's, inner_term; |p| {
    let span = p.as_span();
    as_array!(span in [nxt] = p.into_inner());
    match nxt.as_rule() {
        Rule::infix_term => {
            Ok(InnerTerm::Infix(Arc::new(nxt.try_into()?)))
        }
        Rule::commun_base => {
            as_array!(span in [cmn_rule] = nxt.into_inner());
            match cmn_rule.as_rule(){
                Rule::let_in => {
                    Ok(InnerTerm::LetIn(Arc::new(cmn_rule.try_into()?)))
                },
                Rule::if_then_else => {
                    Ok(InnerTerm::If(Arc::new(cmn_rule.try_into()?)))
                },
                Rule::find_such_that => {
                    Ok(InnerTerm::Fndst(Arc::new(cmn_rule.try_into()?)))
                },
                Rule::quantifier => {
                    Ok(InnerTerm::Quant(Arc::new(cmn_rule.try_into()?)))
                },
                Rule::application => {
                    Ok(InnerTerm::Application(Arc::new(cmn_rule.try_into()?)))
                },
                Rule::macro_application => {
                    Ok(InnerTerm::Macro(Arc::new(cmn_rule.try_into()?)))
                }
                #[allow(unused_variables)]
                r => unreachable_rules!(span, r; let_in, if_then_else, find_such_that, quantifier, application)
            }
        },
        #[allow(unused_variables)]
        r => unreachable_rules!(span, r; infix_term, commun_base)
    }
});

impl<'str, S: Display> Display for InnerTerm<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(ast::InnerTerm, |x| in self => LetIn | If | Fndst | Quant | Application | Infix | Macro
                {x.fmt(f)})
    }
}

impl<'str, S> Not for Term<'str, S>
where
    S: FromStaticString,
{
    type Output = Self;

    fn not(self) -> Self::Output {
        Application::new_app(Default::default(), S::from_static(NOT_NAME), [self]).into()
    }
}

impl<'str, S> BitAnd for Term<'str, S> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::ands([self, rhs])
    }
}

impl<'str, S> BitOr for Term<'str, S> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::ors([self, rhs])
    }
}

impl<'str, S> Shr for Term<'str, S> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Infix {
            span: Default::default(),
            terms: vec![self, rhs],
            operation: Operation::Implies,
        }
        .into()
    }
}

impl<'str, S> Term<'str, S> {
    pub fn ands(args: implvec!(Self)) -> Self {
        Infix {
            span: Default::default(),
            terms: args.into_iter().collect(),
            operation: Operation::And,
        }
        .into()
    }
    pub fn ors(args: implvec!(Self)) -> Self {
        Infix {
            span: Default::default(),
            terms: args.into_iter().collect(),
            operation: Operation::Or,
        }
        .into()
    }

    pub fn letin(var: VariableBinding<'str, S>, t1: Self, t2: Self) -> Self {
        ast::LetIn {
            span: Default::default(),
            var,
            t1,
            t2,
        }
        .into()
    }

    pub fn forall<V>(vars: implvec!(V), arg: Self) -> Self
    where
        VariableBinding<'str, S>: From<V>,
    {
        ast::Quantifier {
            kind: ast::QuantifierKind::Forall,
            span: Default::default(),
            vars: vars.into_iter().collect(),
            content: arg,
        }
        .into()
    }

    pub fn exists<V>(vars: implvec!(V), arg: Self) -> Self
    where
        VariableBinding<'str, S>: From<V>,
    {
        ast::Quantifier {
            kind: ast::QuantifierKind::Exists,
            span: Default::default(),
            vars: vars.into_iter().collect(),
            content: arg,
        }
        .into()
    }
}

pub trait StrApplicable {
    type Term;

    fn app<U, I>(self, args: I) -> Self::Term
    where
        I: IntoIterator<Item = U>,
        Self::Term: From<U>;

    fn to_const(self) -> Self::Term
    where
        Self: Sized,
    {
        self.app([])
    }
}

// TODO: use str location
impl<'a> StrApplicable for &'a str {
    type Term = Term<'a, StrRef<'a>>;

    fn app<U, I>(self, args: I) -> Self::Term
    where
        I: IntoIterator<Item = U>,
        Self::Term: From<U>,
    {
        Function::from_name(self.into()).f(args)
    }
}

// TODO: use str location
impl<'a> StrApplicable for &StrRef<'a> {
    type Term = Term<'a, StrRef<'a>>;

    fn app<U, I>(self, args: I) -> Self::Term
    where
        I: IntoIterator<Item = U>,
        Self::Term: From<U>,
    {
        Function::from_name(self.clone()).f(args)
    }
}

impl<'str, S: Clone> From<VariableBinding<'str, S>> for Term<'str, S> {
    fn from(value: VariableBinding<'str, S>) -> Self {
        Application::ConstVar {
            span: Default::default(),
            content: S::clone(value.variable.name()),
        }
        .into()
    }
}

mod macros {

    /// same as [crate::mforall] but for [Term]
    #[macro_export]
    macro_rules! ast_forall {
        ($($var:ident:$sort:expr),*; $content:block) => {{
            $(
                let $var = $crate::parser::ast::VariableBinding {
                    span: std::default::Default::default(),
                    variable: $crate::parser::ast::Variable::from(utils::string_ref::StrRef::from(std::stringify!($var))),
                    type_name: $crate::parser::ast::TypeName::from(utils::string_ref::StrRef::from($sort))
                };
            )*
            $crate::parser::ast::Term::forall([$($var.clone()),*], {
                $content
            })
        }};
        ($vars:expr, $content:block) => {
            $crate::parser::ast::term::Term::forall($vars, $content)
        }
    }

    /// same as [crate::mexists] but for [Term]
    #[macro_export]
    macro_rules! ast_exists {
        ($($var:ident:$sort:expr),*; $content:block) => {{
            $(
                let $var = $crate::parser::ast::VariableBinding {
                    span: std::default::Default::default(),
                    variable: $crate::parser::ast::Variable::from(utils::string_ref::StrRef::from(std::stringify!($var))),
                    type_name: $crate::parser::ast::TypeName::from(utils::string_ref::StrRef::from($sort))
                };
            )*
            $crate::parser::ast::Term::exists([$($var.clone()),*], {
                $content
            })
        }};
        ($vars:expr, $content:block) => {
            $crate::parser::ast::term::Term::forall($vars, $content)
        }
    }
}
