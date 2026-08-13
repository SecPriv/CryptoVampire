use itertools::Itertools;
use utils::implvec;

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

/// Marks that a type is *almost* free to clone
pub trait LightClone: Clone {}
impl<U: Copy> LightClone for U {}

mod static_rc;
pub(crate) use static_rc::{InnerSmartCow, SmartCow};

#[cfg(test)]
mod test {
    use crate::utils::fresh_name;

    #[test]
    fn test_fresh_name() {
        let a = fresh_name("hey", []);
        let b = fresh_name("hey", ["hey", "hey$0"]);
        let c = fresh_name("", []);

        assert_eq!(&a, "hey");
        assert_eq!(&b, "hey$1");
        assert_eq!(&c, "x");
    }
}
