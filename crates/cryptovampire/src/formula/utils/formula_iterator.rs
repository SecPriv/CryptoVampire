use std::ops::{Deref, DerefMut};

// use crate::problem::problem::Problem;

use bitflags::bitflags;
use itertools::Itertools;
use log::trace;

use crate::formula::{
    formula::{ARichFormula, RichFormula},
    function::{InnerFunction, inner::term_algebra::TermAlgebra},
    manipulation::FrozenSubst,
};
use utils::utils::repeat_n_zip;

bitflags! {
    #[derive(Default )]
    pub struct IteratorFlags: u8 {
        const QUANTIFIER    = 1<<0;
    }
}

/// An iterator over formulas
pub struct FormulaIterator<'bump, V, P, F, I, T>
where
    F: FnMut(P, ARichFormula<'bump>) -> (Option<T>, I),
    I: IntoIterator<Item = (P, ARichFormula<'bump>)>,
    V: DerefMut<Target = Vec<(P, ARichFormula<'bump>)>>
        + Deref<Target = Vec<(P, ARichFormula<'bump>)>>,
    P: Clone,
{
    /// used for the algo, everything there will be iterated on
    pub pile: V,
    /// some extra info to move around. If `None` it will use the last one available
    pub passed_along: Option<P>,
    pub flags: IteratorFlags,
    /// how does this iterator behave ?
    pub f: F,
}

impl<'bump, 'a, V, P, F, I, T> Iterator for FormulaIterator<'bump, V, P, F, I, T>
where
    F: FnMut(P, ARichFormula<'bump>) -> (Option<T>, I),
    I: IntoIterator<Item = (P, ARichFormula<'bump>)>,
    V: DerefMut<Target = Vec<(P, ARichFormula<'bump>)>>
        + Deref<Target = Vec<(P, ARichFormula<'bump>)>>,
    P: Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pile.pop() {
            None => None,
            Some((p, formula)) => {
                match formula.as_ref() {
                    RichFormula::Fun(fun, args) => match fun.as_inner() {
                        InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q))
                            if self.flags.contains(IteratorFlags::QUANTIFIER) =>
                        {
                            trace!("iter thorugh quantifier");
                            let substitution = FrozenSubst::new_from(
                                q.free_variables.iter().map(|v| v.id).collect_vec(),
                                args.iter().cloned().collect_vec(),
                            );
                            let iter = q
                                .get_content()
                                .into_vec()
                                .into_iter()
                                .map(move |f| f.apply_substitution2(&substitution));
                            let iter = repeat_n_zip(p.clone(), iter); //.map(|(p, f)| (p, f));
                            self.pile.extend(iter)
                        }
                        _ => {}
                    },
                    RichFormula::Quantifier(_, args) => {
                        self.pile.extend([(p.clone(), args.shallow_copy())])
                    }
                    _ => {}
                };
                let (ret, add) =
                    (self.f)(self.passed_along.as_ref().unwrap_or(&p).clone(), formula);
                self.pile.extend(add.into_iter());
                if let Some(_) = ret { ret } else { self.next() }
            }
        }
    }
}
