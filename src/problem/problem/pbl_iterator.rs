use super::Problem;

#[derive(Debug, Clone)]
pub struct PblIterator<'bump> {
    pbl: Problem<'bump>,
}

impl<'bump> PblIterator<'bump> {
    pub fn next(&mut self) -> Option<&Problem<'bump>> {
        if let Some(nq) = self.pbl.lemmas.pop_front() {
            self.pbl.query = nq;
            Some(&self.pbl)
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
}

impl<'bump> From<Problem<'bump>> for PblIterator<'bump> {
    fn from(mut pbl: Problem<'bump>) -> Self {
        pbl.lemmas.push_back(pbl.query.clone());
        Self { pbl }
    }
}

impl<'bump> Into<Problem<'bump>> for PblIterator<'bump> {
    fn into(self) -> Problem<'bump> {
        self.pbl
    }
}