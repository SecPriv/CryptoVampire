use std::ops::{BitAnd, BitOr, Not, Shr};

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
}
