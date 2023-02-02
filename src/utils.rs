#[inline(always)]
pub fn replace_if_eq<T: Eq>(a: T, b: T, c: T) -> T {
    if a == b {
        c
    } else {
        a
    }
}

pub fn clone_iter<'a, E, I>(iter: I) -> impl Iterator<Item = E> + 'a
where
    E: Clone + 'a,
    I: Iterator<Item = &'a E> + 'a,
{
    iter.map(|e| e.clone())
}