pub mod axioms;
pub mod declare;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GeneralFile<'bump> {
    pub assertions: Vec<axioms::Axiom<'bump>>,
    pub declarations: Vec<declare::Declaration<'bump>>,
}
