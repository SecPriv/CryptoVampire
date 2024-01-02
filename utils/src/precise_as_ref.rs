/// Because many of my types are actually
/// pseudo `'static` references, this lets
/// one retrive the biggest possible lifetime
/// out of the types.
pub trait PreciseAsRef<'a, T> {
    fn precise_as_ref(&self) -> &'a T;
}

// impl<'a, T, I> AsRef<I> for T where T:PreciseAsRef<'a, T> {
//     fn as_ref(&self) -> &I {
//         self.precise_as_ref()
//     }
// }
