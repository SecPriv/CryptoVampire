use std::iter::Flatten;

#[derive(Debug, Clone, Copy)]
pub struct RunnerSplitter<U> {
    pub vampire: Option<U>,
    pub cvc5: Option<U>,
    pub z3: Option<U>,
}

const LEN: usize = 3;

impl<U> RunnerSplitter<U> {
    #[inline]
    pub fn as_ref(&self) -> RunnerSplitter<&U> {
        self.as_array().map(Option::as_ref).into()
    }

    #[inline]
    pub fn as_mut(&mut self) -> RunnerSplitter<&mut U> {
        self.as_mut_array().map(Option::as_mut).into()
    }

    #[inline]
    pub fn into_array(self) -> [Option<U>; LEN] {
        let Self { vampire, cvc5, z3 } = self;
        [vampire, cvc5, z3]
    }
    #[inline]
    pub fn as_array(&self) -> [&Option<U>; LEN] {
        let Self { vampire, cvc5, z3 } = self;
        [vampire, cvc5, z3]
    }
    #[inline]
    pub fn as_mut_array(&mut self) -> [&mut Option<U>; LEN] {
        let Self { vampire, cvc5, z3 } = self;
        [vampire, cvc5, z3]
    }

    #[allow(dead_code)]
    pub fn map<V>(self, mut f: impl FnMut(U) -> V) -> RunnerSplitter<V> {
        self.into_array().map(|x| x.map(&mut f)).into()
    }

    #[allow(dead_code)]
    pub fn names(&self) -> RunnerSplitter<&'static str> {
        let RunnerSplitter { vampire, cvc5, z3 } = self.as_ref();
        RunnerSplitter {
            vampire: vampire.map(|_| "vampire"),
            cvc5: cvc5.map(|_| "cvc5"),
            z3: z3.map(|_| "z3"),
        }
    }
}

impl<U> From<[Option<U>; LEN]> for RunnerSplitter<U> {
    #[inline]
    fn from([vampire, cvc5, z3]: [Option<U>; 3]) -> Self {
        Self { vampire, cvc5, z3 }
    }
}

impl<U> IntoIterator for RunnerSplitter<U> {
    type Item = U;

    type IntoIter = Flatten<<[Option<U>; 3] as IntoIterator>::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_array().into_iter().flatten()
    }
}

impl<U> Default for RunnerSplitter<U> {
    fn default() -> Self {
        Self {
            vampire: None,
            cvc5: None,
            z3: None,
        }
    }
}
