use cryptovampire_macros::LocationProvider;

#[derive(LocationProvider)]
pub struct Test<'a, T, S> {
    #[provider]
    a: T,
    b: &'a S,
}

#[derive(LocationProvider)]
pub enum Test2<'a, T, S> {
    A(#[provider] T, &'a S),
}

fn test<T>(a: T)
where
    T: std::fmt::Display,
    T: std::fmt::Display,
{
    match Test2::A("a", "b") {
        Test2::A { 0: _, .. } => todo!(),
    }
}
