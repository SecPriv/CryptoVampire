use std::fmt::{Display, Write};
use std::sync::Arc;

use itertools::Itertools;
use log::{debug, log_enabled, trace};
use logic_formula::AsFormula;
use utils::precise_as_ref::PreciseAsRef;
use utils::string_ref::StrRef;
use utils::traits::{NicerError, RefNamed};
use utils::utils::MaybeInvalid;
use utils::{assert_variance, force_lifetime, implderef, implvec, variants_ref};

use super::InnerFunction;
use super::dispacher::Dispacher;
use super::inner::booleans::Booleans;
use super::inner::evaluate::Evaluate;
use super::inner::if_then_else::IfThenElse;
use super::inner::name::Name;
use super::inner::predicate::Predicate;
use super::inner::skolem::Skolem;
use super::inner::step::StepFunction;
use super::inner::subterm::Subterm;
use super::inner::term_algebra::TermAlgebra;
use super::inner::term_algebra::base_function::BaseFunctionTuple;
use super::inner::term_algebra::quantifier::{InnerQuantifier, Quantifier, get_next_quantifer_id};
use super::inner::unused::Tmp;
use super::inner::{self, term_algebra};
use super::signature::{AsFixedSignature, OnlyArgsSignature, OnlyArgsSignatureProxy, Signature};
use super::traits::FixedSignature;
use crate::container::StaticContainer;
use crate::container::allocator::{ContainerTools, Residual};
use crate::container::contained::Containable;
use crate::container::reference::Reference;
use crate::container::utils::NameFinder;
use crate::environement::traits::{KnowsRealm, Realm};
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::function::inner::evaluated_fun::EvaluatedFun;
use crate::formula::function::inner::term_algebra::base_function::BaseFunction;
use crate::formula::function::signature::Lazy::{A, B};
use crate::formula::quantifier;
use crate::formula::sort::Sort;
use crate::formula::sort::sort_proxy::SortProxy;
use crate::formula::sort::sorted::{Sorted, SortedError};
use crate::formula::utils::Applicable;
use crate::formula::variable::Variable;

/// A function is just a pointer to some content in memory.
/// Pieces of it are mutable through a RefCell, other are not.
///
/// Most notable, equality is made on pointers to avoid the possibly
/// convoluted content
///
/// Thus one can copy Function around for more or less free and still
/// carry a lot of information arround within them
pub type Function<'bump> = Reference<'bump, InnerFunction<'bump>>;
// #[derive(Hash, Clone, Copy, PartialEq, Eq)]
// pub struct Function<'bump> {
//     inner: NonNull<Option<InnerFunction<'bump>>>,
//     container: PhantomData<&'bump ()>,
// }

impl<'bump> Containable<'bump> for InnerFunction<'bump> {}

// asssert_trait!(sync_and_send; InnerFunction; Sync, Send);
// assert_variance!(Function);
assert_variance!(InnerFunction);

impl<'bump> Sorted<'bump> for Function<'bump> {
    fn sort(&self, args: &[Sort<'bump>]) -> Result<Sort<'bump>, SortedError> {
        let s = self.signature();
        let partial_s = OnlyArgsSignature::new(args);
        trace!(
            "function check sort:\n\t{}{}\n\targs:[{}]",
            self.name(),
            self.signature().as_display(),
            args.iter().join(", ")
        );
        s.unify(&partial_s, &Realm::default()).debug_continue()?;
        s.out()
            .as_option()
            .ok_or(SortedError::Impossible)
            .debug_continue()
    }
}

macro_rules! container {
    () => {
        &'bump impl ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Self>
    };
    (nf) => {
        &'bump (impl ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Self> + NameFinder<Function<'bump>>)
    }
}

impl<'bump> Function<'bump> {
    pub fn new_from_inner(container: container!(), inner: InnerFunction<'bump>) -> Self {
        container.alloc_inner(inner)
    }

    /// # Safety
    /// do not call `f`, it is not initialised yet
    pub unsafe fn new_cyclic<F, T>(container: container!(), f: F) -> Residual<Self, T>
    where
        F: for<'a> FnOnce(&'a Function<'bump>) -> Residual<InnerFunction<'bump>, T>,
        T: Sized,
    {
        container
            .alloc_cyclic_with_residual(f)
            .expect("function already initialized as")
    }

    pub fn new_spliting(
        container: container!(nf),
        sorts: impl IntoIterator<Item = Sort<'bump>>,
    ) -> Self {
        Self::new_predicate(container, sorts, "split")
    }

    pub fn new_rewrite_function(container: container!(nf), sort: Sort<'bump>) -> Self {
        Self::new_predicate(container, [sort, sort], &format!("rewrite_{}", sort.name()))
    }

    fn new_predicate(
        container: container!(nf),
        sorts: impl IntoIterator<Item = Sort<'bump>>,
        name: &str,
    ) -> Self {
        let name = container.find_free_name(name);
        let inner = InnerFunction::Predicate(Predicate {
            name: name.into(),
            args: sorts.into_iter().collect(),
        });

        container.alloc_inner(inner)
    }

    pub fn new_unused_destructors(container: container!(nf), constructor: Self) -> Vec<Self> {
        let assertion = constructor.can_be_datatype();
        if cfg!(debug_assertions) && !assertion {
            trace!(".");
            debug!("{}", constructor.as_display());
            debug!("{:?}", constructor.as_inner());
        }
        assert!(assertion);

        let o_sort = constructor.fast_outsort().unwrap();
        constructor
            .fast_insort()
            .expect("term algebra should have fast in sorts")
            .iter()
            .enumerate()
            .map(|(i, &s)| {
                let name = container.find_free_name(&format!("dest_{}_{}", constructor.name(), i));
                Self::new_tmp(container, name, [o_sort], s)
            })
            .collect()
    }

    pub fn new_tmp(
        container: container!(),
        name: implderef!(str),
        input_sorts: implvec!(Sort<'bump>),
        output_sort: Sort<'bump>,
    ) -> Self {
        let inner = InnerFunction::Tmp(Tmp {
            name: name.to_string(),
            args: input_sorts.into_iter().collect(),
            sort: output_sort,
        });

        // Self::new_from(container, inner)
        container.alloc_inner(inner)
    }

    pub fn new_skolem(
        container: container!(nf),
        free_sorts: impl IntoIterator<Item = Sort<'bump>>,
        out: Sort<'bump>,
    ) -> Self {
        {
            let name = container.find_free_name("sk_");
            let inner = InnerFunction::Skolem(Skolem {
                name: name.into(),
                args: free_sorts.into_iter().collect(),
                sort: out,
            });
            // Self::new_from(container, inner)
            container.alloc_inner(inner)
        }
    }

    pub fn new_quantifier_from_quantifier(
        container: container!(nf),
        q: quantifier::Quantifier<'bump>,
        arg: ARichFormula<'bump>,
    ) -> Self {
        let id = get_next_quantifer_id();
        // let name = container.find_free_name(&format!("c_{}_{}", q.name(), id));

        let bound_variables = Arc::clone(q.get_variables());

        let free_variables: Arc<[_]> = (&arg)
            .free_vars_iter()
            .unique()
            .filter(|v| !bound_variables.contains(v))
            .collect();

        let inner = match &q {
            quantifier::Quantifier::Exists { .. } => InnerQuantifier::Exists { content: arg },
            quantifier::Quantifier::Forall { .. } => InnerQuantifier::Forall { content: arg },
        };

        let inner = InnerFunction::TermAlgebra(TermAlgebra::Quantifier(Quantifier {
            bound_variables,
            free_variables,
            id,
            inner,
        }));
        container.alloc_inner(inner)
    }

    /// returns the function and the array of free variables
    pub fn new_find_such_that(
        container: container!(nf),
        vars: implvec!(Variable<'bump>),
        condition: ARichFormula<'bump>,
        success: ARichFormula<'bump>,
        faillure: ARichFormula<'bump>,
    ) -> (Self, Arc<[Variable<'bump>]>) {
        let id = get_next_quantifer_id();

        let vars: Arc<[_]> = vars.into_iter().collect();

        let free_variables: Arc<[_]> = [&condition, &success, &faillure]
            .into_iter()
            .flat_map(|f| f.free_vars_iter())
            .unique()
            .filter(|v| !vars.contains(v))
            .collect();

        debug_assert!(
            free_variables.iter().all_unique(),
            "[{}]",
            free_variables.iter().join(", ")
        );

        let inner = InnerFunction::TermAlgebra(TermAlgebra::Quantifier(
            inner::term_algebra::quantifier::Quantifier {
                id,
                bound_variables: vars,
                free_variables: free_variables.clone(),
                inner: inner::term_algebra::quantifier::InnerQuantifier::FindSuchThat {
                    condition,
                    success,
                    faillure,
                },
            },
        ));
        // (Self::new_from(container, inner), free_variables)
        (container.alloc_inner(inner), free_variables)
    }

    pub fn new_user_term_algebra(
        container: container!(),
        name: implderef!(str),
        input_sorts: implvec!(Sort<'bump>),
        output_sort: Sort<'bump>,
    ) -> BaseFunctionTuple<'bump> {
        let input_sorts = input_sorts.into_iter().collect_vec();
        if log_enabled!(log::Level::Trace) {
            let mut str = String::new();
            write!(&mut str, "\t{}(", name.deref()).unwrap();
            for s in &input_sorts {
                write!(&mut str, "{s},").unwrap();
            }
            write!(&mut str, ") -> {output_sort}").unwrap();
            trace!("new_user_term_algebra:\n\t{str}")
        }
        assert!(output_sort.is_term_algebra());

        let Residual {
            content: eval,
            residual: main,
        } = container
            .alloc_cyclic_with_residual(|eval_fun| {
                let main_fun: Function<'bump> = container.alloc_inner(InnerFunction::TermAlgebra(
                    TermAlgebra::Function(BaseFunction {
                        name: name.to_string().into(),
                        args: input_sorts.into_iter().collect(),
                        out: output_sort,
                        eval_fun: *eval_fun,
                    }),
                ));
                let InnerFunction::TermAlgebra(TermAlgebra::Function(_base_main_fun)) =
                    main_fun.precise_as_ref()
                else {
                    unreachable!()
                };

                Residual {
                    content: InnerFunction::EvaluatedFun(EvaluatedFun::new(main_fun)),
                    residual: main_fun,
                }
            })
            .unwrap();
        BaseFunctionTuple { main, eval }
    }

    pub fn fast_outsort(&self) -> Option<Sort<'bump>> {
        self.signature().fast().map(|s| s.fixed_out())
    }
    pub fn fast_insort(&self) -> Option<Vec<Sort<'bump>>> {
        self.signature().fast().map(|s| {
            let tmp = &s;
            tmp.fixed_args().into_iter().collect_vec()
        })
    }

    pub fn signature<'a>(&'a self) -> impl Signature<'bump> + 'bump {
        match self.precise_as_ref() {
            InnerFunction::Bool(x) => B(A(x.signature())),
            InnerFunction::Subterm(x) => B(B(A(x.signature()))),
            InnerFunction::IfThenElse(_x) => B(B(B(IfThenElse::signature()))),
            // fixed signature
            InnerFunction::TermAlgebra(x) => A(x.as_fixed_signature()),
            InnerFunction::Step(x) => A(x.as_fixed_signature()),
            InnerFunction::Evaluate(x) => A(x.as_fixed_signature()),
            InnerFunction::Predicate(x) => A(x.as_fixed_signature()),
            InnerFunction::Tmp(x) => A(x.as_fixed_signature()),
            InnerFunction::Skolem(x) => A(x.as_fixed_signature()),
            InnerFunction::Name(x) => A(x.as_fixed_signature()),
            InnerFunction::EvaluatedFun(x) => A(x.as_fixed_signature()),
        }
    }

    pub fn valid_args(&self, args: implvec!(SortProxy<'bump>)) -> bool {
        let args = args.into_iter().collect_vec();
        self.signature()
            .unify(
                &OnlyArgsSignatureProxy::new(args.as_slice()),
                &Realm::default(),
            )
            .is_ok()
    }

    pub fn name(&self) -> StrRef<'bump> {
        // &self.inner.name
        self.name_ref()
    }

    pub fn apply<'bbump, I>(&self, args: impl IntoIterator<Item = I>) -> RichFormula<'bbump>
    where
        'bump: 'bbump,
        I: Into<ARichFormula<'bbump>>,
    {
        assert!(self.is_valid());
        assert!(!matches!(self.as_inner(), InnerFunction::Tmp(_)));

        RichFormula::Fun(*self, args.into_iter().map_into().collect())
    }

    // pub fn f<'bbump, I>(&self, args: impl IntoIterator<Item = I>) -> ARichFormula<'bbump>
    // where
    //     'bump: 'bbump,
    //     I: Into<ARichFormula<'bbump>>,
    // {
    //     self.apply(args).into_arc()
    // }

    pub fn apply_rf<'bbump>(
        &self,
        args: impl IntoIterator<Item = RichFormula<'bbump>>,
    ) -> RichFormula<'bbump>
    where
        'bump: 'bbump,
    {
        self.apply(args)
    }

    pub fn is_default_subterm(&self) -> bool {
        match self.as_inner() {
            InnerFunction::TermAlgebra(f) => f.is_default_subterm(),
            _ => false,
        }
    }

    /// does this function hide something (ie. quantifier, memory cell, input,...)
    // pub fn need_extraction(&self) -> bool {
    //     match self.as_inner() {
    //         InnerFunction::TermAlgebra(TermAlgebra::Cell(_))
    //         | InnerFunction::TermAlgebra(TermAlgebra::Quantifier(_))
    //         | InnerFunction::TermAlgebra(TermAlgebra::Input(_)) => true,
    //         _ => false,
    //     }
    // }

    pub fn is_builtin(&self) -> bool {
        matches!(
            self.as_inner(),
            InnerFunction::Bool(_) | InnerFunction::IfThenElse(_)
        )
    }

    variants_ref!(InnerFunction, 'bump;
        Bool:Booleans,
        // Nonce:Nonce<'bump>,
        Step:StepFunction<'bump>,
        Subterm:Subterm<'bump>,
        TermAlgebra:TermAlgebra<'bump>,
        IfThenElse:IfThenElse,
        Evaluate:Evaluate<'bump>,
        Predicate:Predicate<'bump>,
        Tmp:Tmp<'bump>,
        Skolem:Skolem<'bump>,
        Name:Name<'bump>,
        EvaluatedFun:EvaluatedFun<'bump>
        // Invalid:InvalidFunction,
    );

    pub fn as_dispacher(self) -> Dispacher<'bump, InnerFunction<'bump>> {
        self.into()
    }

    /// functions that **always** are datatypes
    pub fn is_always_datatype(&self) -> bool {
        matches!(
            self.as_inner(),
            // InnerFunction::Step(StepFunction::Step(_)) |
            InnerFunction::Name(_)
        )
    }

    pub fn can_be_datatype(&self) -> bool {
        self.is_always_datatype() || self.is_term_algebra()
    }

    pub fn as_display(&self) -> DisplayFunction<'bump> {
        DisplayFunction(*self)
    }

    pub fn is_no_op(&self, realm: &impl KnowsRealm) -> bool {
        realm.is_evaluated_realm() && matches!(self.as_inner(), InnerFunction::Evaluate(_))
    }

    pub fn as_quantifer(&self) -> Option<&'bump Quantifier<'bump>> {
        self.precise_as_term_algebra()
            .and_then(|ta| ta.as_quantifier())
    }

    pub fn as_macro(&self) -> Option<term_algebra::step_macro::Macro> {
        self.as_term_algebra().and_then(|f| f.as_macro()).cloned()
    }

    force_lifetime!(Function, 'bump);
}

pub fn new_static_function(inner: InnerFunction<'static>) -> Function<'static> {
    // Function::new_from(&StaticContainer, inner)
    StaticContainer.alloc_inner(inner)
}

pub struct DisplayFunction<'bump>(Function<'bump>);

impl<'bump> Display for DisplayFunction<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.0.name(), self.0.signature().as_display())
    }
}

impl<'bump> Applicable for Function<'bump> {
    type Term = ARichFormula<'bump>;

    fn f<U, I>(self, args: I) -> Self::Term
    where
        I: IntoIterator<Item = U>,
        Self::Term: From<U>,
    {
        self.apply(args).into_arc()
    }
}
