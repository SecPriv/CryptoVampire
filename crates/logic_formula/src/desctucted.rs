use super::*;
pub struct Destructed<F: Formula, I> {
    pub head: Head<F>,
    pub args: I,
}

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

impl<F: Formula, I> PartialEq for Destructed<F, I>
where
    F: PartialEq,
    I: PartialEq,
    F::Fun: PartialEq,
    F::Var: PartialEq,
    F::Quant: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.args == other.args
    }
}

impl<F: Formula, I> Eq for Destructed<F, I>
where
    F: Eq,
    I: Eq,
    F::Fun: Eq,
    F::Var: Eq,
    F::Quant: Eq,
{
}

impl<F: Formula, I> PartialOrd for Destructed<F, I>
where
    F: PartialOrd,
    I: PartialOrd,
    F::Fun: PartialOrd,
    F::Var: PartialOrd,
    F::Quant: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.head.partial_cmp(&other.head) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.args.partial_cmp(&other.args)
    }
}

impl<F: Formula, I> Ord for Destructed<F, I>
where
    F: Ord,
    I: Ord,
    F::Fun: Ord,
    F::Var: Ord,
    F::Quant: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        PartialOrd::partial_cmp(&self, &other).unwrap()
    }
}

impl<F: Formula, I> Debug for Destructed<F, I>
where
    F: Debug,
    I: Debug,
    F::Fun: Debug,
    F::Var: Debug,
    F::Quant: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Destructed")
            .field("head", &self.head)
            .field("args", &self.args)
            .finish()
    }
}

impl<F: Formula, I> Hash for Destructed<F, I>
where
    F: Hash,
    I: Hash,
    F::Fun: Hash,
    F::Var: Hash,
    F::Quant: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.head.hash(state);
        self.args.hash(state);
    }
}

impl<F: Formula, I> Clone for Destructed<F, I>
where
    F: Clone,
    I: Clone,
    F::Fun: Clone,
    F::Var: Clone,
    F::Quant: Clone,
{
    fn clone(&self) -> Self {
        Self {
            head: self.head.clone(),
            args: self.args.clone(),
        }
    }
}
