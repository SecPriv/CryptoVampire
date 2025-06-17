use std::{
    borrow::{Borrow, BorrowMut},
    cell::{Ref, RefCell, RefMut},
    fmt::Display,
    mem::ManuallyDrop,
    rc::{Rc, Weak},
};

use egg::Var;
use log::trace;
use utils::{ereturn_if, ereturn_let};

mod nonce;
pub use nonce::FreshNonce;

use crate::terms::{FOBinder, RecFOFormula, Sort};

#[derive(Debug, Clone)]
struct RefFormulaBuilder(Rc<RefCell<FormulaBuilder>>);

#[derive(Debug)]
struct FormulaBuilder {
    parent: Option<RefFormulaBuilder>,
    mode: Mode,
    content: Vec<RecFOFormula>,
    precomputed: bool,
    staturated: bool,
    condition: Option<Condition>,
    children: Vec<Weak<RefCell<Self>>>,
}

/// A search condition
///
/// ```txt
/// \exists variables:sorts, condition \and ...
/// ```
#[derive(Debug)]
struct Condition {
    /// the actual formula
    pub condition: RecFOFormula,
    /// NB: empty set of variable removes the quantifier instead of simplifying it
    ///
    /// e.g., `(exists () A) => A`
    pub variables: Vec<Var>,
    pub sorts: Vec<Sort>,
    pub quantifier: FOBinder,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
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

impl RefFormulaBuilder {
    pub fn new(mode: Mode, condition: Option<Condition>) -> Self {
        Self(Rc::new(RefCell::new(FormulaBuilder {
            parent: None,
            mode,
            condition,
            children: vec![],
            precomputed: true,
            staturated: false,
            content: vec![],
        })))
    }

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

    pub fn add_node(&self, mode: Mode, condition: Option<Condition>) -> Self {
        let builder: RefFormulaBuilder = RefFormulaBuilder::new(mode, condition);
        self.borrow_mut().children.push(builder.weak());
        {
            let mut builder = builder.borrow_mut();
            builder.parent = Some(self.clone());
            builder.staturated = self.try_evaluate().is_some();
        }
        builder
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
                };
                if !variables.is_empty() {
                    inner = RecFOFormula::bind(quantifier, variables, sorts, inner)
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
        self.staturated = true;
        match &mut self.condition {
            Some(Condition { quantifier, .. }) if quantifier.on_empty() == value => {
                self.staturate(value);
            }
            None => self.staturate(value),
            Some(Condition { condition, .. }) => {
                if let Some(value2) = condition.try_evaluate() {
                    // here quantifier.on_empty() = !value
                    // saturate to `if !value2 { quantifier.on_empty()} else {value}`
                    self.staturate(!(value2 ^ value));
                } else {
                    self.content = vec![value.into()]
                }
            }
        }
    }

    /// erase the condition and set the value of `self` to `value`. This is then
    /// propagated to the parent
    fn staturate(&mut self, value: bool) {
        assert!(self.staturated);
        trace!("staturating to {value}");
        self.precomputed = value;
        self.condition = None;

        ereturn_let!(let Some(parent) = self.parent.as_mut());
        parent.add_leaf(value.into());
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
