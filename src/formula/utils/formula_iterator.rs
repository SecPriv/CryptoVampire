use std::ops::{Deref, DerefMut};

// use crate::problem::problem::Problem;

use bitflags::bitflags;

use crate::{
    formula::{
        self,
        formula::RichFormula,
        function::{
            self,
            term_algebra::{quantifier::Quantifier, TermAlgebra},
            Function, InnerFunction,
        },
        variable::Variable,
    },
    utils::{utils::repeat_n_zip, vecref::VecRef},
};

bitflags! {
    #[derive(Default )]
    pub struct IteratorFlags: u8 {
        const QUANTIFIER    = 1<<0;
    }
}

pub struct FormulaIterator<'bump, 'a, V, P, F, I, T>
where
    F: FnMut(P, &'a RichFormula<'bump>) -> (Option<T>, I),
    I: IntoIterator<Item = (P, &'a RichFormula<'bump>)>,
    V: DerefMut<Target = Vec<(P, &'a RichFormula<'bump>)>>
        + Deref<Target = Vec<(P, &'a RichFormula<'bump>)>>,
    P: Clone,
    'bump: 'a,
{
    /// used for the algo, everything there will be iterated on
    pub pile: V,
    /// some extra info to move around. If `None` it will use the last one available
    pub passed_along: Option<P>,
    pub flags: IteratorFlags,
    /// how does this iterator behave ?
    pub f: F,
}

impl<'bump, 'a, V, P, F, I, T> Iterator for FormulaIterator<'bump, 'a, V, P, F, I, T>
where
    F: FnMut(P, &'a RichFormula<'bump>) -> (Option<T>, I),
    I: IntoIterator<Item = (P, &'a RichFormula<'bump>)>,
    V: DerefMut<Target = Vec<(P, &'a RichFormula<'bump>)>>
        + Deref<Target = Vec<(P, &'a RichFormula<'bump>)>>,
    P: Clone,
    'bump: 'a,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pile.pop() {
            None => None,
            Some((p, formula)) => {
                match formula {
                    RichFormula::Fun(fun, _) => match fun.as_ref() {
                        InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q))
                            if self.flags.contains(IteratorFlags::QUANTIFIER) =>
                        {
                            todo!();
                            let iter = q.get_content();
                            let iter = repeat_n_zip(p.clone(), iter.iter()).map(|(p, f)| (p, *f));
                            self.pile.extend(iter)
                        }
                        _ => {}
                    },
                    RichFormula::Quantifier(_, args) => {
                        self.pile.extend(repeat_n_zip(p.clone(), args.iter()))
                    }
                    _ => {}
                };
                let (ret, add) =
                    (self.f)(self.passed_along.as_ref().unwrap_or(&p).clone(), formula);
                self.pile.extend(add.into_iter());
                if let Some(_) = ret {
                    ret
                } else {
                    self.next()
                }
            }
        }
    }
}

pub struct FormulaIterator2<'bump, 'f> {
    to_do: Vec<&'f RichFormula<'bump>>,
}
