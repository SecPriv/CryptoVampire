use crate::formula::function::Function;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CryptoAssumption {
    EufCmaHash(Function),
}
