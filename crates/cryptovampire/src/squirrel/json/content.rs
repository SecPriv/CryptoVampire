use super::*;
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Content<N, U> {
    pub symb: N,
    pub data: U,
}

impl<N, U> Content<N, U> {
    #[allow(dead_code)]
    pub fn as_ref(&self) -> ContentRef<'_, N, U> {
        ContentRef {
            symb: &self.symb,
            data: &self.data,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentRef<'b, N, U> {
    pub symb: &'b N,
    pub data: &'b U,
}

#[allow(clippy::non_canonical_clone_impl)]
impl<'b, N, U> Clone for ContentRef<'b, N, U> {
    fn clone(&self) -> Self {
        Self {
            symb: self.symb,
            data: self.data,
        }
    }
}

impl<'b, N, U> Copy for ContentRef<'b, N, U> {}

impl<'b, N, U> From<(&'b N, &'b U)> for ContentRef<'b, N, U> {
    fn from((symb, data): (&'b N, &'b U)) -> Self {
        Self { symb, data }
    }
}
