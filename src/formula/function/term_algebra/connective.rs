use crate::formula::function::{
    builtin::{AND, IFF, IMPLIES, NOT, OR},
    Function,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Connective {
    BaseConnective(BaseConnective),
    Equality(Equality),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum BaseConnective {
    And,
    Or,
    Not,
    Implies,
    Iff,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Equality();

impl BaseConnective {
    pub fn evaluated(&self) -> Function<'static> {
        match self {
            BaseConnective::And => AND.clone(),
            BaseConnective::Or => OR.clone(),
            BaseConnective::Not => NOT.clone(),
            BaseConnective::Implies => IMPLIES.clone(),
            BaseConnective::Iff => IFF.clone(),
        }
    }
}
