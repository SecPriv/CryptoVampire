use std::collections::HashSet;

use egg::Var;
pub use exists::*;
use itertools::{chain, izip};
use utils::{ereturn_if, match_as_trait};

use crate::Problem;
use crate::terms::{Function, Sort};
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
    fn bvars(&self) -> &[Var];
    fn cvars(&self) -> &[Var];

    fn top_level_function(&self) -> &Function;
    fn skolems(&self) -> &[Function];
    fn fresh_indices(&self) -> &[Function];

    fn valid(&self, idx: usize, pbl: &Problem) -> bool {
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

    fn bvars_and_sorts(&self) -> impl Iterator<Item = (Var, Sort)> + Clone {
        izip!(self.bvars(), self.bvars_sorts()).map(|(v, s)| (*v, s))
    }

    fn cvars_and_sorts(&self) -> impl Iterator<Item = (Var, Sort)> + Clone {
        izip!(self.cvars(), self.cvars_sorts()).map(|(v, s)| (*v, s))
    }

    fn cvars_as_lang(&self) -> impl Iterator<Item = crate::LangVar> + use<'_, Self> {
        self.cvars().iter().copied().map(egg::ENodeOrVar::Var)
    }

    fn bvars_as_lang(&self) -> impl Iterator<Item = crate::LangVar> + use<'_, Self> {
        self.bvars().iter().copied().map(egg::ENodeOrVar::Var)
    }
}

fn default_valid<Q: QuantifierT>(q: &Q, idx: usize, pbl: &Problem) -> bool {
    // it's at the right index location
    ereturn_if!(
        pbl.functions()
            .quantifiers(q.temporary())
            .get(idx)
            .and_then(|q| Q::try_from_ref(q))
            != Some(q),
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
