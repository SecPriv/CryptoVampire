use std::cell::{Ref, RefCell, RefMut};
use std::fmt::Display;
use std::mem::ManuallyDrop;
use std::rc::{Rc, Weak};

use bon::{Builder, bon, builder};
use egg::Var;
use itertools::chain;
use logic_formula::Formula;
use utils::{ereturn_if, ereturn_let};

use crate::terms::{FOBinder, RecFOFormula, Sort};

declare_trace!($"search");

#[derive(Debug, Clone)]
pub struct RefFormulaBuilder(Rc<RefCell<FormulaBuilder>>);

#[derive(Debug)]
pub struct FormulaBuilder {
    parent: Option<RefFormulaBuilder>,
    mode: Mode,
    content: Vec<RecFOFormula>,
    precomputed: bool,
    staturated: bool,
    condition: Option<Condition>,
    children: Vec<Weak<RefCell<Self>>>,
    /// all the variables bellow `max_var` may have been bound/used
    ///
    /// One shouldn't bound anything bellow
    min_var: u32,
}

/// A search condition
///
/// ```txt
/// \exists variables:sorts, condition \and ...
/// ```
#[derive(Debug, Builder)]
struct Condition {
    /// the actual formula
    #[builder(default= RecFOFormula::True())]
    condition: RecFOFormula,
    /// NB: empty set of variable removes the quantifier instead of simplifying it
    ///
    /// e.g., `(exists () A) => A`
    #[builder(default)]
    variables: Vec<Var>,
    #[builder(default)]
    sorts: Vec<Sort>,
    quantifier: FOBinder,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mode {
    #[default]
    And,
    Or,
}

impl Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Mode::And => write!(f, "and"),
            Mode::Or => write!(f, "or"),
        }
    }
}

#[bon]
impl RefFormulaBuilder {
    #[builder(builder_type = RefFormulaBuilderBuilder)]
    pub fn new(
        mode: Mode,

        parent: Option<&RefFormulaBuilder>,

        condition: Option<RecFOFormula>,
        #[builder(with = <_>::from_iter)] variables: Option<Vec<Var>>,
        #[builder(with = <_>::from_iter)] sorts: Option<Vec<Sort>>,
        quantifier: Option<FOBinder>,

        /// highest variable that we are free to use (i.e., we can fearlessly
        /// bind variables above there)
        ///
        /// **NB**: this value will automatically be corrected to be above any
        /// other referenced variable (by looking a the condition and the
        /// parent)
        #[builder(default = 0)]
        min_var: u32,
    ) -> Self {
        let condition = quantifier.map(|quantifer| {
            Condition::builder()
                .maybe_condition(condition)
                .maybe_sorts(sorts)
                .maybe_variables(variables)
                .quantifier(quantifer)
                .build()
        });

        let min_var = {
            let condition_max_var = condition.as_ref().and_then(|c| {
                chain![
                    c.variables().iter().copied(),
                    c.condition().free_vars_iter()
                ]
                .filter_map(|x| x.as_u32())
                .max()
            });
            let parent_min_var = parent.map(|b| b.min_var());

            chain![[min_var], condition_max_var, parent_min_var]
                .max()
                .unwrap()
        };

        let builder = Self(Rc::new(RefCell::new(FormulaBuilder {
            parent: None,
            mode,
            condition,
            children: vec![],
            precomputed: true,
            staturated: false,
            content: vec![],
            min_var,
        })));

        if let Some(parent) = parent {
            parent.borrow_mut().children.push(builder.weak());
            let mut builder = builder.borrow_mut();
            builder.parent = Some(parent.clone());
            builder.staturated = parent.try_evaluate().is_some();
        }
        builder
    }
}

use ref_formula_builder_builder::IsUnset as RefFormulaBuilderBuilderIsUnset;
impl<'a, S> RefFormulaBuilderBuilder<'a, S>
where
    S: ref_formula_builder_builder::State,
{
    /// Sets the mode to [Mode::And]
    pub fn and(self) -> RefFormulaBuilderBuilder<'a, ref_formula_builder_builder::SetMode<S>>
    where
        S::Mode: RefFormulaBuilderBuilderIsUnset,
    {
        self.mode(Mode::And)
    }

    /// Sets the mode to [Mode::Or]
    pub fn or(self) -> RefFormulaBuilderBuilder<'a, ref_formula_builder_builder::SetMode<S>>
    where
        S::Mode: RefFormulaBuilderBuilderIsUnset,
    {
        self.mode(Mode::Or)
    }
    pub fn forall(
        self,
    ) -> RefFormulaBuilderBuilder<'a, ref_formula_builder_builder::SetQuantifier<S>>
    where
        S::Quantifier: RefFormulaBuilderBuilderIsUnset,
    {
        self.quantifier(FOBinder::Forall)
    }
    pub fn exists(
        self,
    ) -> RefFormulaBuilderBuilder<'a, ref_formula_builder_builder::SetQuantifier<S>>
    where
        S::Quantifier: RefFormulaBuilderBuilderIsUnset,
    {
        self.quantifier(FOBinder::Exists)
    }
}

impl RefFormulaBuilder {
    pub fn weak(&self) -> Weak<RefCell<FormulaBuilder>> {
        Rc::downgrade(&self.0)
    }

    /// tells is any of the `add` will do anything
    pub fn is_saturated(&self) -> bool {
        self.try_evaluate().is_some()
    }

    /// adds to the formula (in a disjonction or a conjunction depending on the mode)
    pub fn add_leaf(&self, content: RecFOFormula) {
        self.borrow_mut().add_leaf(content);
    }

    // pub fn add_node(&self, mode: Mode, condition: Option<Condition>) -> Self {
    //     let builder: RefFormulaBuilder = RefFormulaBuilder::new(mode, condition);
    //     self.borrow_mut().children.push(builder.weak());
    //     {
    //         let mut builder = builder.borrow_mut();
    //         builder.parent = Some(self.clone());
    //         builder.staturated = self.try_evaluate().is_some();
    //     }
    //     builder
    // }
    pub fn add_node(&self) -> RefFormulaBuilderBuilder<'_, ref_formula_builder_builder::SetParent> {
        Self::builder().parent(self)
    }

    /// are we building a conjunction or a disjunction
    pub fn current_mode(&self) -> Mode {
        self.borrow().mode
    }

    pub fn try_saturate(&self, value: bool) {
        self.borrow_mut().try_saturate(value);
    }

    pub fn try_evaluate(&self) -> Option<bool> {
        self.borrow().try_evaluate()
    }

    pub fn borrow(&self) -> Ref<'_, FormulaBuilder> {
        RefCell::borrow(&self.0)
    }

    pub fn borrow_mut(&self) -> RefMut<'_, FormulaBuilder> {
        RefCell::borrow_mut(&self.0)
    }

    pub fn parent(&self) -> Option<Self> {
        self.borrow().parent.clone()
    }

    // get the content bypassing drop
    pub fn into_inner(self) -> Option<FormulaBuilder> {
        ereturn_if!(Rc::strong_count(&self.0) != 1, None);

        let inner = {
            let manually_dropped = ManuallyDrop::new(self);
            // Safety: okay because we'll never be touching "manually_dropped.0" again.
            unsafe { std::ptr::read(&manually_dropped.0) }
        };

        let inner = Rc::into_inner(inner).unwrap(); // cannot fail because of the previous check
        Some(RefCell::into_inner(inner))
    }

    pub fn min_var(&self) -> u32 {
        self.borrow().min_var
    }
}

impl Drop for FormulaBuilder {
    fn drop(&mut self) {
        // this is already taken care of in [Self::saturate]
        ereturn_if!(self.is_saturated());

        ereturn_if!(self.parent.is_none());
        let inner = self.drain_as_formula();

        let parent = self.parent.as_ref().unwrap();
        parent.add_leaf(inner);
    }
}

impl FormulaBuilder {
    fn drain_as_formula(&mut self) -> RecFOFormula {
        assert!(self.children.iter().all(|c| c.upgrade().is_none()));
        let content = std::mem::take(&mut self.content);
        let inner = match self.mode {
            Mode::And => RecFOFormula::and(content),
            Mode::Or => RecFOFormula::or(content),
        };

        match self.condition.take() {
            None => inner,
            Some(Condition {
                condition,
                variables,
                sorts,
                quantifier,
            }) => {
                assert_eq!(variables.len(), sorts.len());

                let mut inner = match quantifier {
                    FOBinder::Forall => condition >> inner,
                    FOBinder::Exists => condition & inner,
                    _ => todo!()
                };
                if !variables.is_empty() {
                    inner = RecFOFormula::bind(quantifier, variables, sorts, [inner])
                }
                inner
            }
        }
    }

    pub fn into_formula(mut self) -> RecFOFormula {
        self.drain_as_formula()
    }

    /// Try to evaluate the formula. Returns [None] if the builtin heuristics can't deduce it
    pub fn try_evaluate(&self) -> Option<bool> {
        // self.borrow().precomputed
        self.is_saturated().then_some(self.precomputed)
    }

    /// tells is any of the `add` will do anything
    pub fn is_saturated(&self) -> bool {
        self.staturated
    }

    /// adds to the formula (in a disjonction or a conjunction depending on the mode)
    pub fn add_leaf(&mut self, content: RecFOFormula) {
        tr!(
            "add_leaf {content}\n(staturated: {}, try_evaluate: {:?})",
            self.is_saturated(),
            content.try_evaluate()
        );
        ereturn_if!(self.is_saturated());

        // checks if we are now saturated
        match (self.mode, content.try_evaluate()) {
            (Mode::And, Some(true)) | (Mode::Or, Some(false)) => {}
            (Mode::And, Some(false)) => self.try_saturate(false),
            (Mode::Or, Some(true)) => self.try_saturate(true),
            _ => self.content.push(content),
        }
    }

    /// sets the builder as saturated
    fn try_saturate(&mut self, value: bool) {
        match &mut self.condition {
            None => self.staturate(value),
            Some(Condition { quantifier, .. }) if quantifier.on_empty() == value => {
                self.staturate(value);
            }
            Some(Condition { condition, .. }) => {
                if let Some(condition_value) = condition.try_evaluate() {
                    // we saturate to (if condition_value { value } else { quantifier.on_empty() })
                    // but quantifier.on_empty() = !value in this branch
                    // condition_value | value | staturated    | !(condition_value ^ value)
                    // 1               | 0     | 0             | 0
                    // 1               | 1     | 1             | 1
                    // 0               | 0     | 1 (empty)     | 1
                    // 0               | 1     | 0 (empty)     | 0
                    let saturate_to = !(condition_value ^ value);
                    self.staturate(saturate_to);
                } else {
                    let mut old_condition = RecFOFormula::True();
                    ::std::mem::swap(condition, &mut old_condition);
                    self.content = vec![old_condition]
                }
            }
        }
    }

    /// erase the condition and set the value of `self` to `value`. This is then
    /// propagated to the parent
    fn staturate(&mut self, value: bool) {
        assert!(
            !self.staturated,
            "the builder was already saturated. Something probably went wrong somewhere"
        );
        self.staturated = true;
        tr!("staturating to {value}");
        self.precomputed = value;
        self.condition = None;

        ereturn_let!(let Some(parent) = self.parent.as_mut());
        parent.add_leaf(value.into());
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }
}

impl Mode {
    /// Returns `true` if the mode is [`And`].
    ///
    /// [`And`]: Mode::And
    #[must_use]
    pub fn is_and(&self) -> bool {
        matches!(self, Self::And)
    }

    /// Returns `true` if the mode is [`Or`].
    ///
    /// [`Or`]: Mode::Or
    #[must_use]
    pub fn is_or(&self) -> bool {
        matches!(self, Self::Or)
    }
}

impl Condition {
    #[allow(dead_code)]
    pub fn condition(&self) -> &RecFOFormula {
        &self.condition
    }

    #[allow(dead_code)]
    pub fn variables(&self) -> &[Var] {
        &self.variables
    }

    #[allow(dead_code)]
    pub fn sorts(&self) -> &[Sort] {
        &self.sorts
    }

    #[allow(dead_code)]
    pub fn quantifier(&self) -> FOBinder {
        self.quantifier
    }
}
