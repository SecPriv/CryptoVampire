use std::cmp::Ordering;

#[inline(always)]
pub fn sort<A: PartialOrd>(a: A, b: A) -> (A, A) {
    sort_by(
        |a, b| PartialOrd::partial_cmp(a, b) == Some(Ordering::Less),
        a,
        b,
    )
}

#[inline]
pub fn sort_by<F, A>(f: F, a: A, b: A) -> (A, A)
where
    F: FnOnce(&A, &A) -> bool,
{
    if f(&a, &b) { (a, b) } else { (b, a) }
}

#[inline]
pub fn sort_by_key<F, U, K>(f: &mut F, a: U, b: U) -> (U, U)
where
    F: FnMut(&U) -> K,
    K: PartialOrd,
{
    sort_by(
        |a, b| PartialOrd::partial_cmp(&f(a), &f(b)) == Some(Ordering::Less),
        a,
        b,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(sort(4, 2), (2, 4));
        assert_eq!(sort(7, 9), (7, 9));
    }
}
