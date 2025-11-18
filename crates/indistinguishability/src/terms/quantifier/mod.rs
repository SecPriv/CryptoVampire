/// Re-exports all public items from the `exists` module, primarily the `Exists` struct.
pub use exists::*;
use itertools::chain;
use utils::{ereturn_if, match_as_trait};

use crate::terms::{Formula, Function, QuantifierIndex, Sort, Variable};
use crate::{Problem, rexp};
mod exists;
mod find;
/// Re-exports all public items from the `find` module, primarily the `FindSuchThat` struct.
pub use find::*;

declare_trace!($"quantifier");

/// Represents a generic quantifier, either existential or a find-such-that.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    /// An existential quantifier.
    Exists(Exists),
    /// A find-such-that quantifier.
    FindSuchThat(FindSuchThat),
}

impl From<FindSuchThat> for Quantifier {
    /// Converts a `FindSuchThat` into a `Quantifier::FindSuchThat`.
    fn from(v: FindSuchThat) -> Self {
        Self::FindSuchThat(v)
    }
}

impl From<Exists> for Quantifier {
    /// Converts an `Exists` into a `Quantifier::Exists`.
    fn from(v: Exists) -> Self {
        Self::Exists(v)
    }
}

/// A trait for common operations on quantifiers.
pub trait QuantifierT: Eq + Sized {
    /// Returns a slice of the bound variables of the quantifier.
    fn bvars(&self) -> &[Variable];
    /// Returns a slice of the context variables of the quantifier.
    fn cvars(&self) -> &[Variable];

    /// Returns a reference to the top-level function associated with this quantifier.
    fn top_level_function(&self) -> &Function;
    /// Returns a slice of the skolem functions associated with this quantifier.
    fn skolems(&self) -> &[Function];
    /// Returns a slice of the fresh index functions associated with this quantifier.
    fn fresh_indices(&self) -> &[Function];

    fn valid(&self, idx: QuantifierIndex, pbl: &Problem) -> bool {
        default_valid(self, idx, pbl)
    }

    /// Returns an iterator over the sorts of the bound variables.
    fn bvars_sorts(&self) -> impl Iterator<Item = Sort> + Clone {
        self.fresh_indices().iter().map(|f| f.signature.output)
    }

    /// Returns an iterator over the sorts of the context variables.
    fn cvars_sorts(&self) -> impl Iterator<Item = Sort> + Clone {
        self.skolems()[0].signature.inputs.iter().copied()
    }

    /// Attempts to downcast a `&Quantifier` to `&Self`.
    fn try_from_ref(q: &Quantifier) -> Option<&Self>;
    /// Attempts to downcast a `&mut Quantifier` to `&mut Self`.
    fn try_from_mut(q: &mut Quantifier) -> Option<&mut Self>;
    /// Returns `true` if the quantifier is temporary, `false` otherwise.
    fn temporary(&self) -> bool;

    /// Returns an iterator over all functions associated with this quantifier (top-level, skolems, fresh indices).
    fn all_functions(&self) -> impl Iterator<Item = &Function> + Clone {
        chain![
            [self.top_level_function()],
            self.skolems(),
            self.fresh_indices()
        ]
    }

    // fn bvars_and_sorts(&self) -> impl Iterator<Item = (Var, Sort)> + Clone {
    //     izip!(self.bvars(), self.bvars_sorts()).map(|(v, s)| (*v, s))
    // }

    // fn cvars_and_sorts(&self) -> impl Iterator<Item = (Var, Sort)> + Clone {
    //     izip!(self.cvars(), self.cvars_sorts()).map(|(v, s)| (*v, s))
    // }

    // fn cvars_as_lang(&self) -> impl Iterator<Item = crate::LangVar> + use<'_, Self> {
    //     self.cvars().iter().copied().map(egg::ENodeOrVar::Var)
    // }

    // fn bvars_as_lang(&self) -> impl Iterator<Item = crate::LangVar> + use<'_, Self> {
    //     self.bvars().iter().copied().map(egg::ENodeOrVar::Var)
    // }

    /// Returns the `QuantifierIndex` of this quantifier.
    fn index(&self) -> QuantifierIndex {
        self.top_level_function().get_quantifier_index().unwrap()
    }

    /// Returns an iterator over the applied skolem functions, where context variables are substituted.
    fn appplied_skolens<'a>(&'a self) -> impl Iterator<Item = Formula> + Clone + use<'a, Self> {
        let args = self.cvars().iter().cloned().map(Formula::Var);
        self.skolems()
            .iter()
            .map(move |sk| rexp!((sk #(args.clone())*)))
    }
}

impl QuantifierT for Quantifier {
    /// Implements `QuantifierT` for the `Quantifier` enum by delegating to the inner `Exists` or `FindSuchThat`.
    fn bvars(&self) -> &[Variable] {
        match_as_trait!(self => { Self::Exists(x) | Self::FindSuchThat(x) => {x.bvars()}})
    }

    fn cvars(&self) -> &[Variable] {
        match_as_trait!(self => { Self::Exists(x) | Self::FindSuchThat(x) => {x.cvars()}})
    }

    fn top_level_function(&self) -> &Function {
        match_as_trait!(self => { Self::Exists(x) | Self::FindSuchThat(x) => {x.top_level_function()}})
    }

    fn skolems(&self) -> &[Function] {
        match_as_trait!(self => { Self::Exists(x) | Self::FindSuchThat(x) => {x.skolems()}})
    }

    fn fresh_indices(&self) -> &[Function] {
        match_as_trait!(self => { Self::Exists(x) | Self::FindSuchThat(x) => {x.fresh_indices()}})
    }

    fn try_from_ref(q: &Quantifier) -> Option<&Self> {
        Some(q)
    }

    fn try_from_mut(q: &mut Quantifier) -> Option<&mut Self> {
        Some(q)
    }

    fn temporary(&self) -> bool {
        match_as_trait!(self => { Self::Exists(x) | Self::FindSuchThat(x) => {x.temporary()}})
    }
}

fn default_valid<Q: QuantifierT>(q: &Q, idx: QuantifierIndex, pbl: &Problem) -> bool {
    ereturn_if!(q.temporary() != idx.temporary, false);
    ereturn_if!(q.index() != idx, false);

    // it's at the right index location
    ereturn_if!(
        idx.get(pbl.functions()).and_then(|q| Q::try_from_ref(q)) != Some(q),
        false
    );

    ereturn_if!(
        q.all_functions()
            .any(|f| f.get_quantifier_index() != Some(idx)),
        false
    );

    ereturn_if!(
        q.top_level_function().arity() != q.bvars().len() + q.cvars().len(),
        false
    );
    ereturn_if!(
        q.skolems().iter().any(|f| f.arity() != q.cvars().len()),
        false
    );
    ereturn_if!(q.fresh_indices().iter().any(|f| f.arity() != 0), false);
    true
}

impl Quantifier {
    /// Returns `true` if the quantifier is temporary, `false` otherwise.
    pub fn temporary(&self) -> bool {
        match_as_trait!(self => {Self::FindSuchThat(x) | Self::Exists(x) => {x.temporary()}})
    }
}
