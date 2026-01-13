use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::sync::OnceLock;

use bon::bon;
use cryptovampire_smt::SortedVar;
use serde::Serialize;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::terms::{Formula, Sort};
use crate::utils::{InnerSmartCow, SmartCow};
use crate::{LangVar, MSmtFormula};

#[derive(Clone, PartialEq, Eq, Hash, Steel)]
pub struct Variable(SmartCow<VariableInner>);

unsafe impl Sync for Variable {}
unsafe impl Send for Variable {}

#[derive(Serialize)]
pub struct VariableInner {
    // /// The smart counter, [None] when the variable is leaked
    // count: Option<AtomicUsize>,
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
        let sort = MaybeOnce::Const(sort);
        Self { sort, unique }
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
        let x = self.get_sort().map(|x| x.short_name()).unwrap_or('x');
        write!(f, "{x}{:x}", self.as_usize())
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let x = self.get_sort().map(|x| x.short_name()).unwrap_or('x');
        let s = self.to_string().to_uppercase();
        let n = s.len().min(5);
        write!(f, "{x}{}", &s[(s.len() - n)..s.len()])
    }
}

impl Variable {
    const fn as_inner_ref(&self) -> &VariableInner {
        self.0.as_ref()
    }

    pub fn as_usize(&self) -> usize {
        self.0.as_usize()
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

    pub(crate) const fn from_const(inner: &'static InnerSmartCow<VariableInner>) -> Self {
        Self(SmartCow::from_static(inner))
    }

    pub const fn const_clone(&self) -> Self {
        Self(self.0.const_clone())
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
        !matches!(self.get_sort(), Some(Sort::Any) | None)
    }

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

    pub fn as_formula(&self) -> Formula {
        Formula::Var(self.clone())
    }

    pub fn into_formula(self) -> Formula {
        Formula::Var(self)
    }

    #[must_use]
    pub const fn is_static(&self) -> bool {
        self.0.is_static()
    }

    /// Makes fresh variables while keeping the information about the variable
    /// (ie. the sort) the same
    pub fn freshen(&self) -> Self {
        Self::fresh().maybe_sort(self.get_sort()).call()
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
        // let inner = Box::new(VariableInner {
        //     count: Some(AtomicUsize::new(1)),
        //     sort: match sort {
        //         Some(x) => MaybeOnce::Const(Some(x)),
        //         _ => MaybeOnce::Dyn(Default::default()),
        //     },
        //     unique: None,
        // });
        // let inner = NonNull::from_ref(Box::leak(inner));
        // Self(inner)

        Self(SmartCow::new(VariableInner {
            sort: match sort {
                Some(x) => MaybeOnce::Const(Some(x)),
                _ => MaybeOnce::Dyn(Default::default()),
            },
            unique: None,
        }))
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
            .register_type::<Self>("Variable?")
    }
}

impl cryptovampire_smt::SortedVar for Variable {
    type Sort = Sort;

    fn sort_ref(&self) -> Cow<'_, Sort> {
        Cow::Owned(self.get_sort().expect("known sort"))
    }

    fn mk(sort: Self::Sort) -> Self
    where
        Self::Sort: Sized,
    {
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

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            std::cmp::Ordering::Equal
        } else {
            self.as_usize().cmp(&other.as_usize())
        }
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
        static TMP: $crate::utils::InnerSmartCow<$crate::terms::variable::VariableInner> =
            $crate::utils::InnerSmartCow::mk_static(
                $crate::terms::variable::VariableInner::new_const(None, Some($crate::fresh!(@str)))
            );
        $crate::terms::variable::Variable::from_const(&TMP)
    }};
    (const $s:expr) => {{
        static TMP: $crate::utils::InnerSmartCow<$crate::terms::variable::VariableInner> =
        $crate::utils::InnerSmartCow::mk_static(
            $crate::terms::variable::VariableInner::new_const(Some({
                #[allow(unused)]
                use$crate::terms::Sort::*;
                $s
            }), Some($crate::fresh!(@str))));
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

    use super::Variable;
    use crate::decl_vars;

    static V1: Variable = fresh!(const Bitstring);
    static V2: Variable = fresh!(const Bitstring);
    static V3: Variable = fresh!(const);
    static V4: Variable = fresh!(const);

    static MANY: &[Variable; 100] = seq!(N in 0..100 { &[#(crate::fresh!(const),)*] });

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
