use super::*;
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Content<'a, U> {
    #[serde(borrow)]
    pub symb: Path<'a>,
    pub data: U,
}

impl<'a, U> Content<'a, U> {
    pub fn as_ref<'b>(&'b self) -> ContentRef<'a, 'b, U> {
        ContentRef {
            symb: &self.symb,
            data: &self.data,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentRef<'a, 'b, U> {
    pub symb: &'b Path<'a>,
    pub data: &'b U,
}

impl<'a, 'b, U> Clone for ContentRef<'a, 'b, U> {
    fn clone(&self) -> Self {
        Self {
            symb: self.symb,
            data: self.data,
        }
    }
}

impl<'a, 'b, U> Copy for ContentRef<'a, 'b, U> {}

impl<'a, 'b, U> From<(&'b Path<'a>, &'b U)> for ContentRef<'a, 'b, U> {
    fn from((symb, data): (&'b Path<'a>, &'b U)) -> Self {
        Self { symb, data }
    }
}
