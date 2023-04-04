use std::ops::{Deref, DerefMut};

// use crate::problem::problem::Problem;

use bitflags::bitflags;

use crate::formula::{
    formula::RichFormula,
    function::{term_algebra::TermAlgebra, InnerFunction},
};

bitflags! {
    #[derive(Default )]
    pub struct IteratorFlags: u8 {
        const QUANTIFIER    = 1<<0;
        const CELLS         = 1<<1;
    }
}

pub struct FormulaIterator<'bump, 'a, V, P, F, I, T>
where
    F: FnMut(P, &'a RichFormula<'bump>) -> (Option<T>, I),
    I: IntoIterator<Item = &'a RichFormula<'bump>>,
    V: DerefMut<Target = Vec<&'a RichFormula<'bump>>> + Deref<Target = Vec<&'a RichFormula<'bump>>>,
    P: Clone,
    'bump: 'a,
{
    pub pile: V,
    pub passed_along: P,
    pub flags: IteratorFlags,
    pub f: F,
}

impl<'bump, 'a, V, P, F, I, T> Iterator for FormulaIterator<'bump, 'a, V, P, F, I, T>
where
    F: FnMut(P, &'a RichFormula<'bump>) -> (Option<T>, I),
    I: IntoIterator<Item = &'a RichFormula<'bump>>,
    V: DerefMut<Target = Vec<&'a RichFormula<'bump>>> + Deref<Target = Vec<&'a RichFormula<'bump>>>,
    P: Clone,
    'bump: 'a,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pile.pop() {
            None => None,
            Some(formula) => {
                match formula {
                    RichFormula::Fun(fun, _) => match fun.as_ref() {
                        InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q))
                            if self.flags.contains(IteratorFlags::QUANTIFIER) =>
                        {
                            self.pile.extend(q.get_content().iter())
                        }
                        _ => {}
                    },
                    RichFormula::Quantifier(_, args) => self.pile.extend(args.iter()),
                    _ => {}
                };
                let (ret, add) = (self.f)(self.passed_along.clone(), formula);
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

// pub(crate) struct FormulaIterator<'a, F, T, V, I>
// where
//     F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, I),
//     I: Iterator<Item = &'a RichFormula>,
//     V: DerefMut<Target = Vec<&'a RichFormula>> + Deref<Target = Vec<&'a RichFormula>>,
// {
//     pile: V,
//     pbl: &'a Problem,
//     flags: IteratorFlags,
//     f: F,
// }

// impl<'a, F, T, V, I> FormulaIterator<'a, F, T, V, I>
// where
//     F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, I),
//     I: Iterator<Item = &'a RichFormula>,
//     V: DerefMut<Target = Vec<&'a RichFormula>> + Deref<Target = Vec<&'a RichFormula>>,
// {
//     pub(crate) fn new(pile: V, pbl: &'a Problem, flags: IteratorFlags, f: F) -> Self {
//         Self {
//             pile,
//             pbl,
//             flags,
//             f,
//         }
//     }
// }

// pub(crate) fn new_formula_iter_vec<'a, F, V, T>(
//     pile: V,
//     pbl: &'a Problem,
//     flags: IteratorFlags,
//     mut f: F,
// ) -> FormulaIterator<
//     'a,
//     impl FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, std::vec::IntoIter<&'a RichFormula>),
//     T,
//     V,
//     std::vec::IntoIter<&'a RichFormula>,
// >
// where
//     F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, Vec<&'a RichFormula>),
//     V: DerefMut<Target = Vec<&'a RichFormula>> + Deref<Target = Vec<&'a RichFormula>>,
// {
//     FormulaIterator {
//         pile,
//         pbl,
//         flags,
//         f: move |a, b| {
//             let (o, r) = f(a, b);
//             (o, r.into_iter())
//         },
//     }
// }

// impl<'a, F, T, V, I> Iterator for FormulaIterator<'a, F, T, V, I>
// where
//     F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, I),
//     I: Iterator<Item = &'a RichFormula>,
//     V: DerefMut<Target = Vec<&'a RichFormula>> + Deref<Target = Vec<&'a RichFormula>>,
// {
//     type Item = T;

//     fn next(&mut self) -> Option<T> {
//         match self.pile.pop() {
//             None => None,
//             Some(formula) => {
//                 match formula {
//                     RichFormula::Fun(fun, _)
//                         if self.flags.contains(IteratorFlags::QUANTIFIER)
//                             && fun.is_from_quantifer() =>
//                     {
//                         let q = self
//                             .pbl
//                             .quantifiers
//                             .iter()
//                             .find(|q| &q.function == fun)
//                             .unwrap();
//                         self.pile.extend(q.iter_content())
//                     }
//                     RichFormula::Quantifier(_, args) => self.pile.extend(args.iter()),
//                     _ => {}
//                 }
//                 let (res, nexts) = (self.f)(formula, self.pbl);
//                 self.pile.extend(nexts);
//                 if let Some(_) = res {
//                     res
//                 } else {
//                     self.next()
//                 }
//             }
//         }
//     }
// }
