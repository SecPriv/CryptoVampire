pub use exists::*;
use itertools::chain;
use utils::{ereturn_if, match_as_trait};

use crate::terms::{Function, QuantifierIndex, RecFOFormula, Sort, Variable};
use crate::{Problem, rexp};
mod exists;
mod find;
pub use find::*;

declare_trace!($"quantifier");

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    Exists(Exists),
    FindSuchThat(FindSuchThat),
}

impl From<FindSuchThat> for Quantifier {
    fn from(v: FindSuchThat) -> Self {
        Self::FindSuchThat(v)
    }
}

impl From<Exists> for Quantifier {
    fn from(v: Exists) -> Self {
        Self::Exists(v)
    }
}

pub trait QuantifierT: Eq + Sized {
    fn bvars(&self) -> &[Variable];
    fn cvars(&self) -> &[Variable];

    fn top_level_function(&self) -> &Function;
    fn skolems(&self) -> &[Function];
    fn fresh_indices(&self) -> &[Function];

    fn valid(&self, idx: QuantifierIndex, pbl: &Problem) -> bool {
        default_valid(self, idx, pbl)
    }

    fn bvars_sorts(&self) -> impl Iterator<Item = Sort> + Clone {
        self.fresh_indices().iter().map(|f| f.signature.output)
    }

    fn cvars_sorts(&self) -> impl Iterator<Item = Sort> + Clone {
        self.skolems()[0].signature.inputs.iter().copied()
    }

    fn try_from_ref(q: &Quantifier) -> Option<&Self>;
    fn try_from_mut(q: &mut Quantifier) -> Option<&mut Self>;
    fn temporary(&self) -> bool;

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

    fn index(&self) -> QuantifierIndex {
        self.top_level_function().get_quantifier_index().unwrap()
    }

    fn appplied_skolens<'a>(
        &'a self,
    ) -> impl Iterator<Item = RecFOFormula> + Clone + use<'a, Self> {
        let args = self.cvars().iter().cloned().map(RecFOFormula::Var);
        self.skolems()
            .iter()
            .map(move |sk| rexp!((sk #(args.clone())*)))
    }
}

impl QuantifierT for Quantifier {
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
    pub fn temporary(&self) -> bool {
        match_as_trait!(self => {Self::FindSuchThat(x) | Self::Exists(x) => {x.temporary()}})
    }
}
