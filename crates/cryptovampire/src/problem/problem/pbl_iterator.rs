use state::State;

use super::Problem;
use crate::formula::function::builtin::TRUE;

mod state {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
    pub enum State {
        NoLemma,
        Done,
        WithLemma,
    }

    impl State {
        pub fn set_to_done(&mut self) {
            *self = State::Done
        }

        /// Returns `true` if the state is [`WithLemma`].
        ///
        /// [`WithLemma`]: State::WithLemma
        #[must_use]
        #[allow(dead_code)]
        pub fn is_with_lemma(&self) -> bool {
            matches!(self, Self::WithLemma)
        }

        /// Returns `true` if the state is [`Done`].
        ///
        /// [`Done`]: State::Done
        #[must_use]
        #[allow(dead_code)]
        pub fn is_done(&self) -> bool {
            matches!(self, Self::Done)
        }

        /// Returns `true` if the state is [`NoLemma`].
        ///
        /// [`NoLemma`]: State::NoLemma
        #[must_use]
        #[allow(dead_code)]
        pub fn is_no_lemma(&self) -> bool {
            matches!(self, Self::NoLemma)
        }
    }
}

#[derive(Debug, Clone)]
pub struct PblIterator<'bump> {
    pbl: Problem<'bump>,
    state: State,
}

#[allow(clippy::should_implement_trait)]
impl<'bump> PblIterator<'bump> {
    pub fn next(&mut self) -> Option<&mut Problem<'bump>> {
        if self.state.is_done() {
            return None;
        }

        if self.state.is_no_lemma() {
            self.state.set_to_done();
            return Some(&mut self.pbl);
        }

        if let Some(nq) = self.pbl.lemmas.pop_front() {
            let old_q = std::mem::replace(&mut self.pbl.query, nq);
            self.pbl.assertions.push(old_q);
            Some(&mut self.pbl)
        } else {
            self.state.set_to_done();
            None
        }
    }

    pub fn current(&self) -> &Problem<'bump> {
        &self.pbl
    }

    pub fn len(&self) -> usize {
        self.pbl.lemmas.len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.pbl.lemmas.is_empty()
    }

    pub fn map<'a, F, U>(&'a mut self, f: &'a mut F) -> InnerPblIter<'bump, 'a, F, U>
    where
        F: for<'b> FnMut(&'b mut Problem<'bump>) -> U,
    {
        InnerPblIter { iter: self, f }
    }

    pub fn assert_one(&self) -> bool {
        matches!(self.state, State::NoLemma)
    }

    pub fn new(mut pbl: Problem<'bump>, with_lemmas: bool) -> Self {
        if with_lemmas {
            pbl.lemmas.push_back(pbl.query.clone());
            pbl.query = TRUE.clone_as_arc();
            Self {
                pbl,
                state: state::State::WithLemma,
            }
        } else {
            Self {
                pbl,
                state: State::NoLemma,
            }
        }
    }
}

pub struct InnerPblIter<'bump, 'a, F, U>
where
    F: for<'b> FnMut(&'b mut Problem<'bump>) -> U,
    'bump: 'a,
{
    iter: &'a mut PblIterator<'bump>,
    f: &'a mut F,
}

impl<'bump, 'a, F, U> Iterator for InnerPblIter<'bump, 'a, F, U>
where
    F: for<'b> FnMut(&'b mut Problem<'bump>) -> U,
    'bump: 'a,
{
    type Item = U;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(&mut self.f)
    }
}
