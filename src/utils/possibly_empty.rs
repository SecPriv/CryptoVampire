use crate::formula::formula::RichFormula;

pub enum PE<'a, 'bump> {
    Empty,
    NotEmpty {
        vec: &'a [RichFormula<'bump>],
        i: usize,
    },
}

impl<'a, 'bump> PE<'a, 'bump> {
    pub fn new(vec: &'a [RichFormula<'bump>]) -> Self {
        Self::NotEmpty { vec, i: 0 }
    }

    pub fn empty() -> Self {
        Self::Empty
    }
}

impl<'a, 'bump> Iterator for PE<'a, 'bump> {
    type Item = &'a RichFormula<'bump>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            PE::Empty => None,
            PE::NotEmpty { vec, i } => vec.get(*i).map(|x| {
                *i += 1;
                x
            }),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            PE::Empty => (0, Some(0)),
            PE::NotEmpty { vec, i } => vec[*i..].iter().size_hint(),
        }
    }
}

impl<'a, 'bump> ExactSizeIterator for PE<'a, 'bump> {
    fn len(&self) -> usize {
        let (lower, upper) = self.size_hint();
        assert_eq!(upper, Some(lower));
        lower
    }
}
