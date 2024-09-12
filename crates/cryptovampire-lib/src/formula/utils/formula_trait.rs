pub trait AsFormula {}

pub trait Applicable {
    type Term;

    fn f<U, I>(self, args: I) -> Self::Term
    where
        I: IntoIterator<Item = U>,
        Self::Term: From<U>;

    fn to_const(self) -> Self::Term
    where
        Self: Sized,
    {
        self.f([])
    }
}
