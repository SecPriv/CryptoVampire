use std::{borrow::Cow, fmt::Debug, rc::Rc, sync::Arc};

use egg::{Analysis, Id, Language};

use crate::{Dependancy, Program, Rule, };

#[cfg(feature = "sync")]
pub struct DRule<L: Language, N: Analysis<L>>(Arc<dyn DynRule<L, N>>);

#[cfg(not(feature = "sync"))]
pub struct DRule<L: Language, N: Analysis<L>>(Rc<dyn DynRule<L, N>>);

pub trait DynRule<L: Language, N: Analysis<L>> {
    /// Searches for matches of the rule in the e-graph and returns the dependencies.
    fn search(&self, prgm: &mut Program<L, N, DRule<L, N>>, goal: Id) -> Dependancy;

    /// Called when the e-graph is rebuilt.
    fn rebuild(&self, _prgm: &Program<L, N, DRule<L, N>>) {}

    /// Debugs the rule.
    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<{}>.", self.name())
    }

    /// Returns the name of the rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("unamed rule")
    }

    fn convert(self) -> DRule<L, N>
    where
        Self: Sized + 'static,
    {
        DRule(Box::<dyn DynRule<_, _>>::from(Box::new(self)).into())
    }
}

impl<L: Language, N: Analysis<L>> Clone for DRule<L, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

trait Tmp {
   type N: Analysis<Self::L>;
   type L: Language;
}

impl<L: Language, N: Analysis<L>> Rule<L, N> for DRule<L, N> {
    fn search(&self, prgm: &mut Program<L, N, Self>, goal: Id) -> Dependancy {
        self.0.search(prgm, goal)
    }

    fn name(&self) -> Cow<'_, str> {
        self.0.name()
    }

    fn rebuild(&self, prgm: &Program<L, N, Self>) {
        self.0.rebuild(prgm);
    }
}


// impl<U:Tmp> Rule<U::L, U::N> for U {
//     fn search(&self, prgm: &mut Program<U::L, U::N, Self>, goal: Id) -> Dependancy {
//         todo!()
//     }
// }

// impl<U:Tmp> !GenralRule<U::L, U::N> for U {}

// impl<L: Language, N: Analysis<L>> GenralRule<L, N> for DRule<L, N> {
//     fn search<R: TryInto<Self>>(&self, prgm: &mut Program<L, N, R>, goal: Id) -> Dependancy {
//         todo!()
//     }
// }

impl<L: Language, N: Analysis<L>> Debug for DRule<L, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("DRule").field(&self.0.name()).finish()
    }
}