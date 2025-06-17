
use egg::{Language, PatternAst};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Subst<V, F>(Vec<(V, F)>);

pub type EggSubst<'a, F> = Subst<egg::Var, PatternAst<F>>;

impl<L> EggSubst<'_, L>
where
    L: Language,
{
    pub fn subst(self, f: PatternAst<L>) -> PatternAst<L> {
        f.apply_pattern_subst(self.0)
    }
}
