use utils::implvec;

/// Checks that `a` and `b` are the same collections up to permutation
///
/// assumes `a` has no duplicates
pub fn same_slice<'a, U: Eq>(a: &'a [U], b: implvec!(&'a U)) -> bool {
    let mut visisted = vec![false; a.len()];

    (
        // b in a
        b.into_iter().all(|x| {
            if let Some(i) = a.iter().position(|y| x == y) {
                visisted[i] = true;
                true
            } else {
                false
            }
        })
    ) && (
        // a in b
        visisted.into_iter().all(|x| x)
    )
}
