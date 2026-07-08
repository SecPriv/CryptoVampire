use std::any::Any;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
#[cfg(not(feature = "sync"))]
use std::rc::Rc;
#[cfg(feature = "sync")]
use std::sync::Arc;

use egg::{Analysis, DidMerge, EGraph, Language};
use serde::Serialize;

use crate::MWeight;
use crate::weight::Weight;

/// The type-erased container for a [`ProofItem`](crate::ProofItem) stored in an
/// e-class' memo cell.
///
/// The analysis (and therefore its [`Data`](egg::Analysis::Data)) is fixed
/// before the rule type `R` is known, so the proof carried by a `Proven` cell is
/// erased to `dyn Any` and downcast back to `ProofItem<R>` on read.
#[cfg(feature = "sync")]
pub(crate) type Erased = Arc<dyn Any + Send + Sync>;
#[cfg(not(feature = "sync"))]
pub(crate) type Erased = Rc<dyn Any>;

/// Erase a concrete value into an [`Erased`] container.
#[cfg(feature = "sync")]
pub(crate) fn erase<T: Any + Send + Sync>(value: T) -> Erased {
    Arc::new(value)
}
#[cfg(not(feature = "sync"))]
pub(crate) fn erase<T: Any>(value: T) -> Erased {
    Rc::new(value)
}

/// A compact, `Copy` view of a [`MemoCell`]'s state, for read-only queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum MemoKind {
    /// No proof attempt has been made yet.
    #[default]
    Unknown,
    /// A proof attempt is currently in progress (used for cycle detection).
    InProgress,
    /// All rules have been tried and none applied.
    Failed,
    /// A proof was found.
    Proven,
}

/// The lattice of memoization states stored in each e-class' analysis data.
///
/// The order is `Unknown < InProgress < Failed < Proven` and merging takes the
/// maximum, with the special case that `Proven ⊕ Failed = Proven` (and emits a
/// warning, since hitting that case usually signals an unsound rule system).
#[derive(Debug)]
enum MemoState {
    Unknown,
    InProgress,
    Failed,
    Proven {
        /// The type-erased [`ProofItem`](crate::ProofItem) justifying the proof.
        proof: Erased,
    },
}

/// Ranks a [`MemoState`] according to the merge lattice.
fn rank(state: &MemoState) -> u8 {
    match state {
        MemoState::Unknown => 0,
        MemoState::InProgress => 1,
        MemoState::Failed => 2,
        MemoState::Proven { .. } => 3,
    }
}

/// Combines two [`MemoState`]s according to the lattice.
///
/// `a` is updated in place to hold the merged result; `b` is consumed.
fn combine(a: &mut MemoState, b: MemoState) -> DidMerge {
    let ra = rank(a);
    let rb = rank(&b);
    if (ra == 3 && rb == 2) || (ra == 2 && rb == 3) {
        log::warn!(
            "golgge: merging a Proven and a Failed e-class; this is sound but very likely \
             indicates an unsound rule system"
        );
    }
    if rb > ra {
        *a = b;
        DidMerge(true, false)
    } else if rb < ra {
        DidMerge(false, true)
    } else {
        // Equal rank: keep `a` (in particular `Proven ⊕ Proven` keeps the first proof).
        DidMerge(false, false)
    }
}

/// The memoization cell stored alongside the user analysis data in each e-class.
///
/// This replaces the previous `FxHashMap<Id, MemoStatus>` memo table: by living
/// in the e-class [`Data`](egg::Analysis::Data), the memo is canonicalized for
/// free by `egg`'s own merge machinery during `rebuild`, instead of needing an
/// `O(memo)` walk on every rebuild.
#[derive(Debug)]
pub struct MemoCell {
    state: MemoState,
}

impl Default for MemoCell {
    fn default() -> Self {
        Self::unknown()
    }
}

impl MemoCell {
    /// Creates a fresh, empty (`Unknown`) cell.
    pub fn unknown() -> Self {
        Self {
            state: MemoState::Unknown,
        }
    }

    /// Returns the current state of the cell.
    pub fn kind(&self) -> MemoKind {
        match self.state {
            MemoState::Unknown => MemoKind::Unknown,
            MemoState::InProgress => MemoKind::InProgress,
            MemoState::Failed => MemoKind::Failed,
            MemoState::Proven { .. } => MemoKind::Proven,
        }
    }

    /// Returns the erased proof, if the cell is `Proven`.
    pub fn proof_ref(&self) -> Option<&Erased> {
        match &self.state {
            MemoState::Proven { proof } => Some(proof),
            _ => None,
        }
    }

    /// Begins a search for the owning e-class.
    ///
    /// - `Started`: the cell was `Unknown` and is now `InProgress`.
    /// - `Cached(true/false)`: the cell already held a terminal result (`Proven`/`Failed`).
    /// - `Cycle`: the cell was already `InProgress` (a cyclic proof attempt).
    pub fn begin_search(&mut self) -> BeginResult {
        match self.state {
            MemoState::Unknown => {
                self.state = MemoState::InProgress;
                BeginResult::Started
            }
            MemoState::InProgress => BeginResult::Cycle,
            MemoState::Failed => BeginResult::Cached(false),
            MemoState::Proven { .. } => BeginResult::Cached(true),
        }
    }

    /// Records a successful proof, applying the merge lattice.
    pub fn set_proven(&mut self, proof: Erased) -> DidMerge {
        combine(&mut self.state, MemoState::Proven { proof })
    }

    /// Records a failed proof, applying the merge lattice.
    pub fn set_failed(&mut self) -> DidMerge {
        combine(&mut self.state, MemoState::Failed)
    }

    /// Merges another cell into this one (used by [`Analysis::merge`]).
    pub fn merge(&mut self, other: MemoCell) -> DidMerge {
        combine(&mut self.state, other.state)
    }

    /// Resets the cell back to `Unknown`.
    pub fn clear(&mut self) {
        self.state = MemoState::Unknown;
    }
}

/// The result of [`MemoCell::begin_search`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BeginResult {
    /// The cell was `Unknown` and is now `InProgress`.
    Started,
    /// The cell already held a terminal result.
    Cached(bool),
    /// The cell was already `InProgress`.
    Cycle,
}

/// The per-e-class data stored by [`GolggeAnalysis`]: the user analysis data
/// alongside the memoization cell.
#[derive(Serialize)]
pub struct GData<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    /// The user-provided analysis data.
    #[serde(skip)]
    pub memo: MemoCell,
    /// The user-provided analysis data.
    pub user: UA::Data,
    #[serde(skip)]
    _p: PhantomData<fn(L)>,
}

impl<UA, L> Debug for GData<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GData")
            .field("memo", &self.memo)
            .field("user", &self.user)
            .finish()
    }
}

/// Trait giving access to the [`MemoCell`] inside an analysis' [`Data`](Analysis::Data).
///
/// Implemented for [`GData`]; `Program` requires `N::Data: HasMemo`.
pub trait HasMemo {
    /// Returns the memo cell.
    fn memo(&self) -> &MemoCell;
    /// Returns the memo cell, mutably.
    fn memo_mut(&mut self) -> &mut MemoCell;
}

impl<UA, L> HasMemo for GData<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    fn memo(&self) -> &MemoCell {
        &self.memo
    }
    fn memo_mut(&mut self) -> &mut MemoCell {
        &mut self.memo
    }
}

/// The user-facing analysis trait.
///
/// It mirrors [`egg::Analysis`] (with the e-graph typed as
/// [`GolggeAnalysis<Self>`]) plus the weight accessors from [`WeightedAnalysis`].
/// Downstream crates implement this for their analysis and let [`GolggeAnalysis`]
/// provide the actual `egg::Analysis` impl (which transparently adds the
/// [`MemoCell`]).
pub trait UserAnalysis<L: Language>: Sized {
    /// The per-e-class data for this analysis.
    type Data: Debug;

    /// Makes new analysis data for an e-node. Mirrors [`Analysis::make`].
    fn make(egraph: &mut EGraph<L, GolggeAnalysis<Self, L>>, enode: &L) -> Self::Data;

    /// Merges two data when their e-classes merge. Mirrors [`Analysis::merge`].
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge;

    /// Hook called after a merge. Mirrors [`Analysis::modify`].
    #[allow(unused_variables)]
    fn modify(egraph: &mut EGraph<L, GolggeAnalysis<Self, L>>, id: egg::Id) {}

    /// The weight type used to order proofs.
    type Weight: Weight;
    /// Returns the weight stored in the given data.
    fn get_weight(data: &Self::Data) -> Self::Weight;
}

/// The `egg::Analysis` adapter that wraps a [`UserAnalysis`] and transparently
/// maintains a [`MemoCell`] per e-class.
///
/// It [`Deref`](std::ops::Deref)s to the inner `UA`, so existing
/// `egraph.analysis.<user_method>()` accessors keep working unchanged.
#[derive(Serialize)]
pub struct GolggeAnalysis<UA, L: Language>
where
    UA: UserAnalysis<L>,
{
    #[serde(skip)]
    inner: UA,
    #[serde(skip)]
    _p: PhantomData<fn(L)>,
}

impl<UA, L: Language> GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L>,
{
    /// Wraps a user analysis into the golgge adapter.
    pub fn new(inner: UA) -> Self {
        Self {
            inner,
            _p: PhantomData,
        }
    }

    /// Returns a reference to the inner user analysis.
    pub fn inner(&self) -> &UA {
        &self.inner
    }

    /// Returns a mutable reference to the inner user analysis.
    pub fn inner_mut(&mut self) -> &mut UA {
        &mut self.inner
    }
}

impl<UA, L> std::ops::Deref for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    type Target = UA;
    fn deref(&self) -> &UA {
        &self.inner
    }
}

impl<UA, L> std::ops::DerefMut for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    fn deref_mut(&mut self) -> &mut UA {
        &mut self.inner
    }
}

impl<UA, L> Debug for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L> + Debug,
    L: Language,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<UA, L> Default for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L> + Default,
    L: Language,
{
    fn default() -> Self {
        Self::new(UA::default())
    }
}

impl<UA, L> Clone for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L> + Clone,
    L: Language,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _p: PhantomData,
        }
    }
}

impl<UA, L> Analysis<L> for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    type Data = GData<UA, L>;

    fn make(egraph: &mut EGraph<L, Self>, enode: &L) -> Self::Data {
        let user = UA::make(egraph, enode);
        GData {
            memo: MemoCell::unknown(),
            user,
            _p: PhantomData,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let du = self.inner.merge(&mut a.user, b.user);
        let dm = a.memo.merge(b.memo);
        DidMerge(du.0 || dm.0, du.1 || dm.1)
    }

    fn modify(egraph: &mut EGraph<L, Self>, id: egg::Id) {
        UA::modify(egraph, id);
    }
}

/// A trait for `egg::Analysis` implementations that provide a weight for e-classes.
///
/// This is what rule types (e.g. [`PrologRule`](crate::PrologRule)) consume;
/// [`GolggeAnalysis`] implements it by delegating to the inner [`UserAnalysis`].
pub trait WeightedAnalysis<L>: egg::Analysis<L>
where
    L: Language,
{
    /// The type used to represent the weight.
    type Weight: Weight;
    /// Returns the weight of the given `Data`.
    fn get_weight(data: &Self::Data) -> Self::Weight;
}

impl<L: Language> WeightedAnalysis<L> for () {
    type Weight = ();
    fn get_weight(_: &Self::Data) -> Self::Weight {}
}

/// Trivial `UserAnalysis`: no per-node data, no weights. The `egg::Analysis`
/// work is done by wrapping it in [`GolggeAnalysis`].
impl<L: Language> UserAnalysis<L> for () {
    type Data = ();
    fn make(_egraph: &mut EGraph<L, GolggeAnalysis<Self, L>>, _enode: &L) -> Self::Data {}
    fn merge(&mut self, _a: &mut Self::Data, _b: Self::Data) -> DidMerge {
        DidMerge(false, false)
    }
    type Weight = ();
    fn get_weight(_data: &Self::Data) -> Self::Weight {}
}

impl<UA, L> WeightedAnalysis<L> for GolggeAnalysis<UA, L>
where
    UA: UserAnalysis<L>,
    L: Language,
{
    type Weight = UA::Weight;
    fn get_weight(data: &Self::Data) -> Self::Weight {
        UA::get_weight(&data.user)
    }
}

// --- The legacy golgge analysis, now a `UserAnalysis` ---

/// Stores the weight and representant for an e-class.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Data<L> {
    /// The weight of the e-class.
    pub weight: MWeight,
    /// The representant of the e-class.
    pub representant: L,
}

/// A [`UserAnalysis`] that tracks the minimum weight and a representant for each
/// e-class.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct MAnalysis<L>
where
    L: Language,
{
    /// A map from discriminant to its weight.
    pub weight_map: HashMap<L::Discriminant, MWeight>,
}

impl<L> UserAnalysis<L> for MAnalysis<L>
where
    L: Language,
    L::Discriminant: Hash,
{
    type Data = Data<L>;

    fn make(egraph: &mut EGraph<L, GolggeAnalysis<Self, L>>, enode: &L) -> Self::Data {
        let weight = enode
            .children()
            .iter()
            .map(|id| egraph[*id].data.user.weight)
            .sum::<MWeight>()
            + egraph
                .analysis
                .weight_map
                .get(&enode.discriminant())
                .copied()
                .unwrap_or(Weight::min());
        let representant = enode.clone();
        Data {
            weight,
            representant,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let Data {
            weight: wa,
            representant: ra,
        } = a;
        let Data {
            weight: wb,
            representant: rb,
        } = b;
        if wa.decreases(&wb) {
            DidMerge(false, true)
        } else {
            *wa = wb;
            *ra = rb;
            DidMerge(true, false)
        }
    }

    type Weight = MWeight;
    fn get_weight(data: &Self::Data) -> Self::Weight {
        data.weight
    }
}
