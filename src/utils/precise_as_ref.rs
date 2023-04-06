pub trait PreciseAsRef<'a, T> {
    fn precise_as_ref(&self) -> &'a T;
}