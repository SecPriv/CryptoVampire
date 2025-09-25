use std::fmt::{Debug, Display};
use std::ptr::NonNull;
use std::sync::OnceLock;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::input::Registerable;
use crate::terms::Sort;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Steel)]
pub struct Variable(NonNull<VariableInner>);

unsafe impl Sync for Variable {}
unsafe impl Send for Variable {}

pub struct VariableInner {
    /// The smart counter, [None] when the variable is leaked
    count: Option<AtomicUsize>,

    sort: MaybeOnce<Sort>,
    unique: Option<&'static str>,
}

#[derive(Debug, Clone)]
enum MaybeOnce<T> {
    Const(Option<T>),
    Dyn(OnceLock<T>),
}

impl Clone for Variable {
    fn clone(&self) -> Self {
        let inner = self.as_ptr();
        match &inner.count {
            Some(c) => {
                // same implementation as `Arc` hence why the `Rela`
                let old_count = c.fetch_add(1, Relaxed);

                if old_count >= usize::MAX {
                    panic!("too many references for the counter")
                }
            }
            None => {}
        }
        Self(self.0)
    }
}

impl VariableInner {
    pub const fn new_const(sort: Option<Sort>, unique: Option<&'static str>) -> Self {
        let count = None;
        let sort = MaybeOnce::Const(sort);
        Self {
            count,
            sort,
            unique,
        }
    }
}

impl Drop for Variable {
    fn drop(&mut self) {
        // same implementation as `Arc`
        {
            let inner = self.as_ptr();
            let Some(count) = &inner.count else {
                return;
            };

            if count.fetch_sub(1, Release) != 1 {
                return;
            }
            std::sync::atomic::fence(Acquire);
        }

        let inner = unsafe { Box::from_raw(self.0.as_mut()) };
        drop(inner);
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "x{:}", self.as_usize())
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.to_string();
        let n = s.len().min(5);
        write!(f, "{}", &s[..n])
    }
}

impl Variable {
    fn as_ptr(&self) -> &VariableInner {
        unsafe { self.0.as_ref() }
    }

    pub fn as_usize(&self) -> usize {
        self.0.as_ptr() as usize
    }

    pub const fn from_const(inner: &'static VariableInner) -> Self {
        assert!(matches!(inner.count, None));
        Self(NonNull::from_ref(inner))
    }

    pub fn get_sort(&self) -> Option<Sort> {
        match &self.as_ptr().sort {
            MaybeOnce::Const(x) => *x,
            MaybeOnce::Dyn(once_lock) => once_lock.get().copied(),
        }
    }

    pub fn set_sort(&self, sort: Sort) -> Result<(), Sort> {
        match &self.as_ptr().sort {
            MaybeOnce::Dyn(l) => l.set(sort),
            _ => Err(sort),
        }
    }

    fn steel_fresh() -> Self {
        Self::fresh().call()
    }

    fn steel_fresh_sort(s: Sort) -> Self {
        Self::fresh().sort(s).call()
    }
}

#[bon]
impl Variable {
    #[builder]
    pub fn fresh(sort: Option<Sort>) -> Self {
        let inner = Box::new(VariableInner {
            count: Some(AtomicUsize::new(1)),
            sort: match sort {
                Some(x) => MaybeOnce::Const(Some(x)),
                _ => MaybeOnce::Dyn(Default::default()),
            },
            unique: None,
        });
        let inner = NonNull::from_ref(Box::leak(inner));
        Self(inner)
    }
}

impl From<Variable> for egg::Var {
    fn from(value: Variable) -> Self {
        egg::Var::from_usize(
            value
                .as_usize()
        )
    }
}

impl Registerable for Variable {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module)
            .register_fn("mk-fresh-var", Self::steel_fresh)
            .register_fn("mk-fresh-var-w-sort", Self::steel_fresh_sort)
    }
}

macro_rules! mk_fresh_var {
    // (@path) => {
    //   $crate::terms::formula::variable
    // };
    (@str) => {
        std::concat![std::file!(), ":", std::line!(), ":", std::column!()]
    };

    () => {{
        static TMP: $crate::terms::variable::VariableInner =
        $crate::terms::variable::VariableInner::new_const(None, Some(mk_fresh_var!(@str)));
        $crate::terms::variable::Variable::from_const(&TMP)
    }};
    ($s:expr) => {{
        static TMP: $crate::terms::variable::VariableInner =
        $crate::terms::variable::VariableInner::new_const(Some($s), Some(mk_fresh_var!(@str)));
        $crate::terms::variable::Variable::from_const(&TMP)
    }};
}

#[macro_export]
macro_rules! fresh {
    () => {
        $crate::terms::Variable::fresh().call()
    };
    ($sort:expr) => {
        $crate::terms::Variable::fresh().sort($sort).call()
    };
}

use bon::{bon, builder};
pub(crate) use mk_fresh_var as mk_fresh_static_var;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use super::Variable;
    use crate::terms::Sort;

    static V1: Variable = mk_fresh_var!(Sort::Bitstring);
    static V2: Variable = mk_fresh_var!(Sort::Bitstring);
    static V3: Variable = mk_fresh_var!();
    static V4: Variable = mk_fresh_var!();

    macro_rules! mk_vars {
        (@ ) => {0};
        (@ $ta:tt $($t:tt)*)  => {1 + mk_vars!(@ $($t)*)};
        (# $i:ident $($t:tt)*) => {
            static $i: [Variable; mk_vars!(@ $($t)*)] =
                [
                    $(mk_vars!($t)),*
                ];
        };
        ($t:tt) => {mk_fresh_var!()}
    }

    mk_vars!(# MANY x x x x x x x x x x x x x x x x );

    #[test]
    fn statics_diff1() {
        assert!([&V1, &V2.clone(), &V3, &V4].iter().all_unique());
        assert_ne!(&V1, &V2);
        assert_ne!(&V1, &V2.clone());
        assert_ne!(&V3, &V4);
    }

    #[test]
    fn statics_diff2() {
        assert!(MANY.iter().all_unique())
    }

    #[test]
    fn diff1() {
        static N: usize = 400;
        let vars = (0..N).map(|_| Variable::fresh().call()).collect_vec();

        for ((ix, x), (iy, y)) in vars
            .iter()
            .enumerate()
            .cartesian_product(vars.iter().enumerate())
        {
            if ix != iy {
                assert_ne!(x, y)
            } else {
                assert_eq!(x, y)
            }
        }
        assert!(vars.iter().all_unique())
    }

    #[test]
    fn same() {
        static N: usize = 400;
        let v = fresh!();
        let vars = (0..N).map(|_| v.clone()).collect_vec();

        for x in vars {
            assert_eq!(x, v)
        }
    }
}
