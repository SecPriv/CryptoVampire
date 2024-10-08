use std::ops::{BitAnd, BitOr, Not, Shr};

use cryptovampire_lib::formula::utils::Applicable;
use term_algebra::connective::NOT_NAME;

use super::*;

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
            inner: InnerTerm::Application(Arc::new(Application::Application {
                span: Default::default(),
                function: Function::from_name(s),
                args: Default::default(),
            })),
        }
    }
}

impl<'a, S: Display> Display for Term<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

macro_rules! from_i_term {
    ($v:ident, $t:ident) => {
        impl<'a, S> From<$t<'a, S>> for Term<'a, S> {
            fn from(value: $t<'a, S>) -> Self {
                Term {
                    span: value.span,
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
impl<'a, S> From<Application<'a, S>> for Term<'a, S> {
    fn from(value: Application<'a, S>) -> Self {
        Term {
            span: value.span(),
            inner: InnerTerm::Application(Arc::new(value)),
        }
    }
}

/// Gather many rules at once, namely:
/// - [Rule::infix_term]
/// - [Rule::commun_base]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum InnerTerm<'a, S = &'a str> {
    LetIn(Arc<LetIn<'a, S>>),
    If(Arc<IfThenElse<'a, S>>),
    Fndst(Arc<FindSuchThat<'a, S>>),
    Quant(Arc<Quantifier<'a, S>>),
    Application(Arc<Application<'a, S>>),
    Infix(Arc<Infix<'a, S>>),
    Macro(Arc<AppMacro<'a, S>>),
}
boiler_plate!(InnerTerm<'s>, 's, inner_term; |p| {
    let span: Location = p.as_span().into();
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
                r => unreachable_rules!(span, r; let_in, if_then_else, find_such_that, quantifier, application)
            }
        },
        r => unreachable_rules!(span, r; infix_term, commun_base)
    }
});
impl<'a, S: Display> Display for InnerTerm<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match_as_trait!(ast::InnerTerm, |x| in self => LetIn | If | Fndst | Quant | Application | Infix | Macro
                {x.fmt(f)})
    }
}

impl<'a, S> Not for Term<'a, S>
where
    S: FromStaticString,
{
    type Output = Self;

    fn not(self) -> Self::Output {
        Application::new_app(S::from_static(NOT_NAME), [self]).into()
    }
}

impl<'a, S> BitAnd for Term<'a, S> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::ands([self, rhs])
    }
}

impl<'a, S> BitOr for Term<'a, S> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::ors([self, rhs])
    }
}

impl<'a, S> Shr for Term<'a, S> {
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

impl<'a, S> Term<'a, S> {
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

    pub fn letin(var: VariableBinding<'a, S>, t1: Self, t2: Self) -> Self {
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
        VariableBinding<'a, S>: From<V>,
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
        VariableBinding<'a, S>: From<V>,
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

impl<'a, S: Clone> From<VariableBinding<'a, S>> for Term<'a, S> {
    fn from(value: VariableBinding<'a, S>) -> Self {
        Application::ConstVar {
            span: Default::default(),
            content: S::clone(value.variable.name()),
        }
        .into()
    }
}

mod macros {

    /// same as [cryptovampire_lib::mforall] but for [Term]
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

    /// same as [cryptovampire_lib::mexists] but for [Term]
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
