pub trait FromWith<T, U> {
    fn from_with(other: T, arg: U) -> Self;
}

pub trait IntoWith<T, U> {
    fn into_with(self, arg: U) -> T;
}

// impl<T, U, V> IntoWith<T, U> for V where T: FromWith<V, U> {
//     fn into_with(self, arg: U) -> T {
//         T::from_with(self, arg)
//     }
// }

impl<T, U, V> FromWith<V, U> for T
where
    V: IntoWith<T, U>,
{
    fn from_with(other: V, arg: U) -> Self {
        other.into_with(arg)
    }
}
