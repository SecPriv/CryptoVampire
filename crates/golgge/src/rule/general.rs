use std::{borrow::Cow, default};

use egg::{Analysis, Id, Language};

use crate::{Dependancy, Program, Rule, rule::dynamic::DRule};

pub trait GenralRule<L: Language, N: Analysis<L>>: Sized {
    /// Searches for matches of the rule in the e-graph and returns the dependencies.
    fn search<R: TryInto<Self>>(&self, prgm: &mut Program<L, N, R>, goal: Id) -> Dependancy;

    /// Called when the e-graph is rebuilt.
    fn rebuild<R: TryInto<Self>>(&self, _prgm: &Program<L, N, R>) {}

    /// Debugs the rule.
    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<{}>.", self.name())
    }

    /// Returns the name of the rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("unamed rule")
    }
}

impl<L: Language, N: Analysis<L>, U: GenralRule<L, N>> Rule<L, N> for U {
    fn search(&self, prgm: &mut Program<L, N, Self>, goal: Id) -> Dependancy {
        GenralRule::search(self, prgm, goal)
    }

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<{}>.", self.name())
    }

    fn rebuild(&self, _prgm: &Program<L, N, Self>) {}

    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("unamed rule")
    }
}
