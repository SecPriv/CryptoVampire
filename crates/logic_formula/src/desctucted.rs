use super::*;
/// Represents a destructured formula, separating its head from its arguments.
pub struct Destructed<F: AsFormula, I> {
    /// The head of the formula.
    pub head: Head<F>,
    /// The arguments of the formula.
    pub args: I,
}

/// A macro to generate trait bounds for `Destructed`.
#[allow(unused_macros)]
macro_rules! mk_bounds {
($f:ty, $i:ty : $t:ty; $($tt:tt)*) => {
      impl<F:Formula, I> $t for Destructed<F, I>
      where
          $f : $t,
          $i : $t,
          $f::Fun : $t,
          $f::Var : $t,
          $f::Quant : $t {
              $($tt)*
          }
  };
}

impl<F: AsFormula, I> PartialEq for Destructed<F, I>
where
    F: PartialEq,
    I: PartialEq,
    F::Fun: PartialEq,
    F::Var: PartialEq,
    F::Quant: PartialEq,
{
    /// Compares two `Destructed` instances for equality.
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.args == other.args
    }
}

impl<F: AsFormula, I> Eq for Destructed<F, I>
where
    F: Eq,
    I: Eq,
    F::Fun: Eq,
    F::Var: Eq,
    F::Quant: Eq,
{
}

impl<F: AsFormula, I> PartialOrd for Destructed<F, I>
where
    F: PartialOrd,
    I: PartialOrd,
    F::Fun: PartialOrd,
    F::Var: PartialOrd,
    F::Quant: PartialOrd,
{
    /// Compares two `Destructed` instances for partial order.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.head.partial_cmp(&other.head) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.args.partial_cmp(&other.args)
    }
}

impl<F: AsFormula, I> Ord for Destructed<F, I>
where
    F: Ord,
    I: Ord,
    F::Fun: Ord,
    F::Var: Ord,
    F::Quant: Ord,
{
    /// Compares two `Destructed` instances for total order.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        PartialOrd::partial_cmp(&self, &other).unwrap()
    }
}

impl<F: AsFormula, I> Debug for Destructed<F, I>
where
    F: Debug,
    I: Debug,
    F::Fun: Debug,
    F::Var: Debug,
    F::Quant: Debug,
{
    /// Formats the `Destructed` instance for debugging.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Destructed")
            .field("head", &self.head)
            .field("args", &self.args)
            .finish()
    }
}

impl<F: AsFormula, I> Hash for Destructed<F, I>
where
    F: Hash,
    I: Hash,
    F::Fun: Hash,
    F::Var: Hash,
    F::Quant: Hash,
{
    /// Hashes the `Destructed` instance.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.head.hash(state);
        self.args.hash(state);
    }
}

impl<F: AsFormula, I> Clone for Destructed<F, I>
where
    F: Clone,
    I: Clone,
    F::Fun: Clone,
    F::Var: Clone,
    F::Quant: Clone,
{
    /// Clones the `Destructed` instance.
    fn clone(&self) -> Self {
        Self {
            head: self.head.clone(),
            args: self.args.clone(),
        }
    }
}
