use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::ptr::NonNull;
use std::sync::OnceLock;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use bon::{bon, builder};
use serde::Serialize;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::{LangVar, MSmtFormula};
use crate::input::Registerable;
use crate::terms::Sort;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Steel)]
pub struct Variable(NonNull<VariableInner>);

unsafe impl Sync for Variable {}
unsafe impl Send for Variable {}

#[derive(Serialize)]
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

impl<T> MaybeOnce<T> {
    pub fn as_option(&self) -> Option<&T> {
        match self {
            Self::Const(x) => x.as_ref(),
            Self::Dyn(x) => x.get(),
        }
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
    const fn as_inner_ref(&self) -> &VariableInner {
        unsafe { self.0.as_ref() }
    }

    pub fn as_usize(&self) -> usize {
        self.0.as_ptr() as usize
    }

    /// Convertes to `egg` variables
    /// 
    /// (this is needed when iteracting with `egg` or `golgge`)
    pub fn as_egg(&self) -> egg::Var {
        egg::Var::from_usize(self.as_usize())
    }

    /// Convertes to `egg` variables in a `egg::Language`
    /// 
    /// (this is needed when iteracting with `egg` or `golgge`)
    pub fn as_lang_var(&self) -> LangVar {
        egg::ENodeOrVar::Var(self.as_egg())
    }

    pub const fn from_const(inner: &'static VariableInner) -> Self {
        assert!(matches!(inner.count, None));
        Self(NonNull::from_ref(inner))
    }

    pub const fn const_clone(&self) -> Self {
        match self.is_static() {
            true => Self(self.0),
            _ => panic!("not static"),
        }
    }

    #[must_use]
    pub fn get_sort(&self) -> Option<Sort> {
        match &self.as_inner_ref().sort {
            MaybeOnce::Const(x) => *x,
            MaybeOnce::Dyn(once_lock) => once_lock.get().copied(),
        }
    }

    #[must_use]
    pub fn has_sort(&self) -> bool {
        self.get_sort().is_some()
    }

    #[must_use]
    pub fn has_smt_sort(&self) -> bool {
        match self.get_sort() {
            Some(Sort::Any) | None => false,
            _ => true,
        }
    }

    #[must_use]
    pub fn maybe_set_sort(&self, sort: Option<Sort>) -> Result<(), Option<Sort>> {
        match (sort, &self.as_inner_ref().sort) {
            (None, _) => Ok(()),
            (Some(sort), MaybeOnce::Dyn(l)) => match l.set(sort) {
                Err(orginal_sort) if sort != orginal_sort => Err(Some(orginal_sort)),
                _ => Ok(()),
            },
            (x, MaybeOnce::Const(x_init)) => {
                if &x == x_init {
                    Ok(())
                } else {
                    Err(*x_init)
                }
            }
        }
    }

    #[must_use]
    pub const fn is_static(&self) -> bool {
        self.as_inner_ref().count.is_none()
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

impl Clone for Variable {
    fn clone(&self) -> Self {
        let inner = self.as_inner_ref();
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

impl Drop for Variable {
    fn drop(&mut self) {
        // same implementation as `Arc`
        {
            let inner = self.as_inner_ref();
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

impl From<Variable> for egg::Var {
    fn from(value: Variable) -> Self {
        egg::Var::from_usize(value.as_usize())
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

impl cryptovampire_smt::SortedVar for Variable {
    type Sort = Sort;

    fn sort_ref(&self) -> Cow<'_, Sort> {
        Cow::Owned(self.get_sort().expect("known sort"))
    }
    
    fn mk(sort: Self::Sort) -> Self where Self::Sort: Sized {
        crate::fresh!(sort)
    }
}

impl Serialize for Variable {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_inner_ref().serialize(serializer)
    }
}

impl<T: Serialize> Serialize for MaybeOnce<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_option().serialize(serializer)
    }
}

impl From<Variable> for MSmtFormula {
    fn from(value: Variable) -> Self {
        Self::Var(value)
    }
}

impl From<&Variable> for MSmtFormula {
    fn from(value: &Variable) -> Self {
        Self::Var(value.clone())
    }
}

impl From<&Variable> for Variable {
    fn from(value: &Variable) -> Self {
        value.clone()
    }
}

#[macro_export]
macro_rules! fresh {
    () => {
        $crate::terms::Variable::fresh().call()
    };

    (@str) => {
        std::concat![std::file!(), ":", std::line!(), ":", std::column!()]
    };
    (const) => {{
        static TMP: $crate::terms::variable::VariableInner =
        $crate::terms::variable::VariableInner::new_const(None, Some($crate::fresh!(@str)));
        $crate::terms::variable::Variable::from_const(&TMP)
    }};
    (const $s:expr) => {{
        static TMP: $crate::terms::variable::VariableInner =
        $crate::terms::variable::VariableInner::new_const(Some({
            #[allow(unused)]
            use$crate::terms::Sort::*;
            $s
        }), Some($crate::fresh!(@str)));
        $crate::terms::variable::Variable::from_const(&TMP)
    }};
    ($sort:expr) => {
        $crate::terms::Variable::fresh().sort({
            #[allow(unused)]
            use $crate::terms::Sort::*;
            $sort
        }).call()
    };
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use seq_macro::seq;

    use crate::decl_vars;

    use super::Variable;

    static V1: Variable = fresh!(const Bitstring);
    static V2: Variable = fresh!(const Bitstring);
    static V3: Variable = fresh!(const);
    static V4: Variable = fresh!(const);


    static MANY : &[Variable; 100] = seq!(N in 0..100 { &[#(crate::fresh!(const),)*] });

    decl_vars!(const A, B, C, D:Nonce,);

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
    fn static_diff3() {
        assert!([&A, &C, &B, &D].iter().all_unique())
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
