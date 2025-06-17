// pub(crate) mod vampire;
pub(crate) use crate::vampire::rule;
pub use rule::VampireRule;

pub(crate) mod base_rules;
pub(crate) mod prf;

mod fresh;
pub use fresh::FreshNonce;
