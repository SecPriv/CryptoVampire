use std::cell::{Ref, RefCell, RefMut};
use std::fmt::Display;
use std::ops::Deref;
use std::rc::{Rc, Weak};

use bitflags::Flags;
use bon::{Builder, bon, builder};
use log::trace;
use utils::{ereturn_if, ereturn_let};

use crate::terms::{FOBinder, Formula, Variable};

declare_trace!($"search");

#[derive(Debug)]
pub struct RefFormulaBuilder<A: FormulaBuilderAux = DefaultAux>(Rc<RefCell<FormulaBuilder<A>>>);

#[derive(Debug)]
pub struct FormulaBuilder<A: FormulaBuilderAux = DefaultAux> {
    /// The parent builder, if this is a nested builder.
    parent: Option<RefFormulaBuilder<A>>,
    /// The logical mode of this builder (And/Or).
    mode: Mode,
    /// Some flags directing the search.
    ///
    /// Currently used to restrict going though certain terms (e.g., inputs and cells)
    flags: FormulaBuilderFlags,
    /// The collected formulas within this builder.
    content: Vec<Formula>,
    /// Whether the formula has been precomputed.
    precomputed: bool,
    /// Whether the builder has been saturated (i.e., its result is final).
    staturated: bool,
    /// The optional condition associated with this builder.
    condition: Option<Condition>,
    /// Weak references to child builders.
    children: Vec<Weak<RefCell<Self>>>,

    aux: A,

    name: Variable,
}

/// A search condition
///
/// ```txt
/// \exists variables:sorts, condition \and ...
/// ```
#[derive(Debug, Builder)]
struct Condition {
    /// the actual formula
    #[builder(default= Formula::True())]
    condition: Formula,
    /// NB: empty set of variable removes the quantifier instead of simplifying it
    ///
    /// e.g., `(exists () A) => A`
    #[builder(default)]
    variables: Vec<Variable>,
    quantifier: FOBinder,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mode {
    /// Represents a logical AND operation.
    #[default]
    And,
    /// Represents a logical OR operation.
    Or,
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct FormulaBuilderFlags: u8 {
        const NO_THROUGH_DIRECT_MEMORY_CELL = 1 << 0;
        const NO_THROUGH_PRED_MEMORY_CELL = 1 << 1;
        const NO_THROUGH_EXEC = 1 << 2 ;
        const NO_THROUGH_FRAME = 1 << 3;

        const NO_THROUGH_ALL_MEMORY_CELL = FormulaBuilderFlags::NO_THROUGH_DIRECT_MEMORY_CELL.bits() | FormulaBuilderFlags::NO_THROUGH_PRED_MEMORY_CELL.bits();
        const NO_THROUGH_PREVIOUS_BODY = FormulaBuilderFlags::NO_THROUGH_EXEC.bits() | FormulaBuilderFlags::NO_THROUGH_FRAME.bits();
        const NO_RECURSION = FormulaBuilderFlags::NO_THROUGH_ALL_MEMORY_CELL.bits() | FormulaBuilderFlags::NO_THROUGH_PREVIOUS_BODY.bits();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
pub struct DefaultAux;

#[derive(Debug, Clone, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
pub enum SaturationCommand {
    SaturateTo(bool),
    Insert(Formula),
    #[default]
    Skip,
}

pub trait FormulaBuilderAux: Sized {
    fn merge(&mut self, mode: Mode, content: Vec<Formula>) -> Formula;

    fn try_evaluate(&self, fb: &FormulaBuilder<Self>, content: Formula) -> SaturationCommand;
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
impl<A: FormulaBuilderAux + Clone + Default> RefFormulaBuilder<A> {
    #[builder(builder_type = RefFormulaBuilderBuilder)]
    pub fn new(
        /// Defaults to `empty`, even when `parent` is set
        #[builder(field)]
        flags: FormulaBuilderFlags,
        /// Defaults to `And`
        #[builder(default)]
        mode: Mode,
        parent: Option<&RefFormulaBuilder<A>>,
        condition: Option<Formula>,
        #[builder(with = <_>::from_iter, default)] variables: Vec<Variable>,
        /// Defaults to `Forall` when a condition is set
        mut quantifier: Option<FOBinder>,
        #[builder(default = true)] clone_parent_aux: bool,
        aux: Option<A>,
    ) -> Self {
        if quantifier.is_none() && condition.is_some() {
            quantifier = Some(FOBinder::Forall)
        }

        let condition = quantifier.map(|quantifer| {
            Condition::builder()
                .maybe_condition(condition)
                .variables(variables)
                .quantifier(quantifer)
                .build()
        });

        let aux = match (aux, parent) {
            (Some(aux), _) => aux,
            (_, Some(parent)) if clone_parent_aux => parent.0.borrow().aux.clone(),
            _ => Default::default(),
        };

        let builder = Self(Rc::new(RefCell::new(FormulaBuilder {
            parent: None,
            mode,
            condition,
            children: vec![],
            precomputed: true,
            staturated: false,
            content: vec![],
            aux,
            flags,
            name: Variable::fresh().call(),
        })));
        trace!(
            "spwaned builder {:?} with flags {:?}",
            builder.0.borrow().name,
            flags
        );

        if let Some(parent) = parent {
            parent.add_children(builder.clone());
            let mut builder = builder.borrow_mut();
            builder.parent = Some(parent.clone());
            builder.staturated = parent.try_evaluate().is_some();
        }
        builder
    }
}

use ref_formula_builder_builder::IsUnset as RefFormulaBuilderBuilderIsUnset;
impl<'a, A, S> RefFormulaBuilderBuilder<'a, A, S>
where
    S: ref_formula_builder_builder::State,
    A: FormulaBuilderAux + Clone + Default,
{
    /// Sets the mode to [Mode::And]
    pub fn and(self) -> RefFormulaBuilderBuilder<'a, A, ref_formula_builder_builder::SetMode<S>>
    where
        S::Mode: RefFormulaBuilderBuilderIsUnset,
    {
        self.mode(Mode::And)
    }

    /// Sets the mode to [Mode::Or]
    pub fn or(self) -> RefFormulaBuilderBuilder<'a, A, ref_formula_builder_builder::SetMode<S>>
    where
        S::Mode: RefFormulaBuilderBuilderIsUnset,
    {
        self.mode(Mode::Or)
    }
    /// Sets the quantifier for the condition to `FOBinder::Forall`.
    pub fn forall(
        self,
    ) -> RefFormulaBuilderBuilder<'a, A, ref_formula_builder_builder::SetQuantifier<S>>
    where
        S::Quantifier: RefFormulaBuilderBuilderIsUnset,
    {
        self.quantifier(FOBinder::Forall)
    }
    /// Sets the quantifier for the condition to `FOBinder::Exists`.
    pub fn exists(
        self,
    ) -> RefFormulaBuilderBuilder<'a, A, ref_formula_builder_builder::SetQuantifier<S>>
    where
        S::Quantifier: RefFormulaBuilderBuilderIsUnset,
    {
        self.quantifier(FOBinder::Exists)
    }

    pub fn add_flag(mut self, flag: FormulaBuilderFlags) -> RefFormulaBuilderBuilder<'a, A, S> {
        self.flags |= flag;
        self
    }

    pub fn remove_flag(mut self, flag: FormulaBuilderFlags) -> RefFormulaBuilderBuilder<'a, A, S> {
        self.flags.remove(flag);
        self
    }
}

impl<A: FormulaBuilderAux> RefFormulaBuilder<A> {
    /// Creates a new [`RefFormulaBuilder`] with `self` as a parent and inheriting the `flags`. This function returns a `RefFormulaBuilderBuilder`
    pub fn add_node(
        &self,
    ) -> RefFormulaBuilderBuilder<'_, A, ref_formula_builder_builder::SetParent>
    where
        A: Clone + Default,
    {
        trace!("add node to {:?}", self.dgb_name());
        Self::builder().parent(self).add_flag(self.flags())
    }

    pub fn add_children(&self, child: Self) {
        trace!(
            "adding child {:?} to {:?}",
            child.dgb_name(),
            self.dgb_name()
        );
        self.0.borrow_mut().children.push(child.weak());
    }

    pub(crate) fn dgb_name(&self) -> Variable {
        self.0.borrow().name.clone()
    }

    /// Returns a weak reference to the inner `FormulaBuilder`.
    pub fn weak(&self) -> Weak<RefCell<FormulaBuilder<A>>> {
        Rc::downgrade(&self.0)
    }

    /// tells is any of the `add` will do anything
    pub fn is_saturated(&self) -> bool {
        self.try_evaluate().is_some()
    }

    pub fn is_and(&self) -> bool {
        self.borrow().mode == Mode::And
    }

    pub fn is_or(&self) -> bool {
        self.borrow().mode == Mode::Or
    }

    /// adds to the formula (in a disjonction or a conjunction depending on the mode)
    pub fn add_leaf(&self, content: Formula) {
        self.borrow_mut().add_leaf(content);
    }

    /// are we building a conjunction or a disjunction
    pub fn current_mode(&self) -> Mode {
        self.borrow().mode
    }

    pub fn flags(&self) -> FormulaBuilderFlags {
        self.borrow().flags()
    }

    /// Attempts to saturate the builder with a given boolean value.
    ///
    /// This propagates the saturation up the parent chain.
    pub fn try_saturate(&self, value: bool) {
        self.borrow_mut().try_saturate(value);
    }

    pub fn try_evaluate(&self) -> Option<bool> {
        self.borrow().try_evaluate()
    }

    /// Immutably borrows the inner `FormulaBuilder`.
    pub fn borrow(&self) -> Ref<'_, FormulaBuilder<A>> {
        RefCell::borrow(&self.0)
    }

    /// Mutably borrows the inner `FormulaBuilder`.
    pub fn borrow_mut(&self) -> RefMut<'_, FormulaBuilder<A>> {
        RefCell::borrow_mut(&self.0)
    }

    /// Returns the parent `RefFormulaBuilder`, if any.
    pub fn parent(&self) -> Option<Self> {
        self.borrow().parent.clone()
    }

    /// get the content bypassing drop
    pub fn into_inner(self) -> Option<FormulaBuilder<A>> {
        Some(RefCell::into_inner(Rc::into_inner(self.0)?))
    }

    /// Clones `self` if it is an and or makes a new node set to `and` if it
    /// isn't. Beware this simply calls `add_node`.
    pub fn ensure_and(&self) -> Self
    where
        A: FormulaBuilderAux + Clone + Default,
    {
        if self.is_and() {
            self.clone()
        } else {
            self.add_node().and().build()
        }
    }
}

impl<A: FormulaBuilderAux> Drop for FormulaBuilder<A> {
    /// Implements the `drop` logic for `FormulaBuilder`.
    ///
    /// If the builder is not saturated, it drains its content into a formula
    /// and adds it as a leaf to its parent builder.
    fn drop(&mut self) {
        // this is already taken care of in [Self::saturate]
        ereturn_if!(self.is_saturated());

        ereturn_if!(self.parent.is_none());
        let inner = self.drain_as_formula();

        let parent = self.parent.as_ref().unwrap();
        trace!(target: "search", "dropping formula builder {:?} with flags {:?}", self.name, self.flags());
        parent.add_leaf(inner);
    }
}

impl<A: FormulaBuilderAux> FormulaBuilder<A> {
    /// Drains the content of the builder and converts it into a `RecFOFormula`.
    ///
    /// This consumes the content and applies the builder's mode and condition.
    fn drain_as_formula(&mut self) -> Formula {
        assert!(self.children.iter().all(|c| c.upgrade().is_none()));
        let content = std::mem::take(&mut self.content);

        let inner = self.aux.merge(self.mode, content);

        match self.condition.take() {
            None => inner,
            Some(Condition {
                condition,
                variables,
                quantifier,
            }) => {
                let mut inner = match quantifier {
                    FOBinder::Forall => condition >> inner,
                    FOBinder::Exists => condition & inner,
                    FOBinder::FindSuchThat => {
                        unreachable!("type error, cannot be a find such that")
                    }
                };
                if !variables.is_empty() {
                    inner = Formula::bind(quantifier, variables, [inner])
                }
                inner
            }
        }
    }

    pub fn into_formula(mut self) -> Formula {
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
    pub fn add_leaf(&mut self, content: Formula) {
        tr!(
            "add_leaf {content}\n(staturated: {}, try_evaluate: {:?})",
            self.is_saturated(),
            content.try_evaluate()
        );
        debug_assert_ok!(content.type_check().recurse(true).call());

        ereturn_if!(self.is_saturated());

        // checks if we are now saturated
        let sat = self.aux.try_evaluate(&*self, content);
        match sat {
            SaturationCommand::SaturateTo(v) => self.try_saturate(v),
            SaturationCommand::Insert(formula) => self.content.push(formula),
            SaturationCommand::Skip => {}
        }
    }

    /// sets the builder as saturated
    /// Attempts to saturate the builder with a given boolean value.
    ///
    /// If saturation occurs, it propagates the value up to the parent builder.
    pub fn try_saturate(&mut self, value: bool) {
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
                    let mut old_condition = Formula::True();
                    ::std::mem::swap(condition, &mut old_condition);
                    self.content = vec![old_condition]
                }
            }
        }
    }

    /// erase the condition and set the value of `self` to `value`. This is then
    /// propagated to the parent
    /// Sets the builder as saturated with a given boolean value.
    ///
    /// This clears the condition and propagates the saturation to the parent.
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

    pub fn flags(&self) -> FormulaBuilderFlags {
        self.flags
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
    pub fn condition(&self) -> &Formula {
        &self.condition
    }

    #[allow(dead_code)]
    pub fn variables(&self) -> &[Variable] {
        &self.variables
    }

    #[allow(dead_code)]
    pub fn quantifier(&self) -> FOBinder {
        self.quantifier
    }
}

impl FormulaBuilderAux for DefaultAux {
    fn merge(&mut self, mode: Mode, content: Vec<Formula>) -> Formula {
        match mode {
            Mode::And => Formula::and(content),
            Mode::Or => Formula::or(content),
        }
    }

    fn try_evaluate(&self, fb: &FormulaBuilder<Self>, content: Formula) -> SaturationCommand {
        use SaturationCommand::*;
        match (fb.mode, content.try_evaluate()) {
            (Mode::And, Some(true)) | (Mode::Or, Some(false)) => Skip,
            (Mode::And, Some(false)) => SaturateTo(false),
            (Mode::Or, Some(true)) => SaturateTo(true),
            _ => Insert(content),
        }
    }
}

impl<A: FormulaBuilderAux> Clone for RefFormulaBuilder<A> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
