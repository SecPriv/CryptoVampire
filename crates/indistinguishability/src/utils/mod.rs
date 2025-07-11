
use itertools::Itertools;
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

/// Get an name based on `name` that doesn't clash with anything in `avoid`
///
/// If name is empty, it assumes it is `"x"`
///
/// ```ignore
/// # use crate::utils::*;
/// let a = fresh_name("hey", []);
/// let b = fresh_name("hey", ["hey", "hey#0"]);
/// let c = fresh_name("", []);
///
/// assert_eq!(&a, "hey");
/// assert_eq!(&b, "hey#1");
/// assert_eq!(&c, "x");
/// ```
pub fn fresh_name<'a, 'b>(name: &str, avoid: implvec!(&'b str)) -> String {
    if name.is_empty() {
        return fresh_name("x", avoid);
    }

    let avoid = avoid
        .into_iter()
        .filter(|s| s.starts_with(name))
        .collect_vec();

    let mut i = 0u32;
    let mut nname = name.to_owned();
    while avoid.contains(&nname.as_str()) {
        nname = format!("{name}${i:}");
        i += 1;
    }
    nname
}

#[cfg(test)]
mod test {
    use crate::utils::fresh_name;

    #[test]
    fn test_fresh_name() {
        let a = fresh_name("hey", []);
        let b = fresh_name("hey", ["hey", "hey#0"]);
        let c = fresh_name("", []);

        assert_eq!(&a, "hey");
        assert_eq!(&b, "hey#1");
        assert_eq!(&c, "x");
    }
}
