use std::collections::HashMap;
use std::hash::Hash;

use egg::Language;

use crate::MWeight;
use crate::weight::Weight;

/// Stores the weight and representant for an e-class.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Data<L> {
    /// The weight of the e-class.
    weight: MWeight,
    /// The representant of the e-class.
    representant: L,
}

/// An `egg::Analysis` that tracks the minimum weight and a representant for each e-class.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MAnalysis<L>
where
    L: Language,
{
    /// A map from discriminant to its weight.
    pub weight_map: HashMap<L::Discriminant, MWeight>,
}

impl<L: Language> Default for MAnalysis<L> {
    /// Returns a default `MAnalysis` instance.
    fn default() -> Self {
        Self {
            weight_map: Default::default(),
        }
    }
}

impl<L> egg::Analysis<L> for MAnalysis<L>
where
    L: Language,
    L::Discriminant: Hash,
{
    /// The data associated with each e-class.
    type Data = Data<L>;

    /// Creates the initial `Data` for an enode.
    fn make(egraph: &mut egg::EGraph<L, Self>, enode: &L) -> Self::Data {
        let weight = enode
            .children()
            .iter()
            .map(|id| egraph[*id].data.weight)
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

    /// Merges two `Data` instances, keeping the one with the lower weight.
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        let Data {
            weight: wa,
            representant: ra,
        } = a;
        let Data {
            weight: wb,
            representant: rb,
        } = b;
        if wa.decreases(&wb) {
            egg::DidMerge(false, true)
        } else {
            *wa = wb;
            *ra = rb;
            egg::DidMerge(true, false)
        }
    }
}

/// A trait for `egg::Analysis` implementations that provide a weight for e-classes.
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
    /// The unit type, indicating no weight.
    type Weight = ();

    /// Returns the unit value.
    fn get_weight(_: &Self::Data) -> Self::Weight {}
}

impl<L> WeightedAnalysis<L> for MAnalysis<L>
where
    L: Language,
    L::Discriminant: Hash,
{
    /// The `MWeight` type.
    type Weight = MWeight;

    /// Returns the weight from the given `Data`.
    fn get_weight(data: &Self::Data) -> Self::Weight {
        data.weight
    }
}
