use crate::formula::function::builtin::TRUE;

use super::Problem;

#[derive(Debug, Clone)]
pub struct PblIterator<'bump> {
    pbl: Problem<'bump>,
}

impl<'bump> PblIterator<'bump> {
    pub fn next(&mut self) -> Option<&mut Problem<'bump>> {
        if let Some(nq) = self.pbl.lemmas.pop_front() {
            let old_q = std::mem::replace(&mut self.pbl.query, nq);
            self.pbl.assertions.push(old_q);
            Some(&mut self.pbl)
        } else {
            None
        }
    }

    pub fn current(&self) -> &Problem<'bump> {
        &self.pbl
    }

    pub fn len(&self) -> usize {
        self.pbl.lemmas.len()
    }

    #[allow(private_interfaces)]
    pub fn map<'a, F, U>(&'a mut self, f: &'a mut F) -> InnerPblIter<'bump, 'a, F, U>
    where
        F: for<'b> FnMut(&'b mut Problem<'bump>) -> U,
    {
        InnerPblIter { iter: self, f }
    }
}

struct InnerPblIter<'bump, 'a, F, U>
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
    'bump:'a,
{
    type Item = U;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(&mut self.f)
    }
}

impl<'bump> From<Problem<'bump>> for PblIterator<'bump> {
    fn from(mut pbl: Problem<'bump>) -> Self {
        pbl.lemmas.push_back(pbl.query.clone());
        pbl.query = TRUE.clone_as_arc();
        Self { pbl }
    }
}

impl<'bump> Into<Problem<'bump>> for PblIterator<'bump> {
    fn into(self) -> Problem<'bump> {
        self.pbl
    }
}
