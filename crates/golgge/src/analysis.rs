use std::collections::HashMap;
use std::hash::Hash;

use egg::Language;

use crate::MWeight;
use crate::weight::Weight;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Data<L> {
    weight: MWeight,
    representant: L,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MAnalysis<L>
where
    L: Language,
{
    pub weight_map: HashMap<L::Discriminant, MWeight>,
}

impl<L: Language> Default for MAnalysis<L> {
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
    type Data = Data<L>;

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

pub trait WeightedAnalysis<L>: egg::Analysis<L>
where
    L: Language,
{
    type Weight: Weight;
    fn get_weight(data: &Self::Data) -> Self::Weight;
}

impl<L: Language> WeightedAnalysis<L> for () {
    type Weight = ();

    fn get_weight(_: &Self::Data) -> Self::Weight {}
}

impl<L> WeightedAnalysis<L> for MAnalysis<L>
where
    L: Language,
    L::Discriminant: Hash,
{
    type Weight = MWeight;

    fn get_weight(data: &Self::Data) -> Self::Weight {
        data.weight
    }
}
