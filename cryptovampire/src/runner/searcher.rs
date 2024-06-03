use cryptovampire_lib::{
    environement::environement::Environement, formula::formula::RichFormula, problem::crypto_assumptions::{CryptoAssumption, EufCmaMac, EufCmaSign, IntCtxt}
};

pub trait InstanceSearcher<'bump> {
    fn search_instances(&self, str: &str, env:&Environement<'bump>) -> Vec<RichFormula<'bump>>;
}

impl<'bump> InstanceSearcher<'bump> for CryptoAssumption<'bump> {
    fn search_instances(&self, str: &str, env:&Environement<'bump>) -> Vec<RichFormula<'bump>> {
        match self {
            CryptoAssumption::EufCmaMac(a) => a.search_instances(str, env),
            CryptoAssumption::EufCmaSign(a) => a.search_instances(str, env),
            CryptoAssumption::IntCtxtSenc(a) => a.search_instances(str, env),
            CryptoAssumption::Nonce(_) | CryptoAssumption::MemoryCell(_) => vec![],
        }
    }
}

impl<'bump> InstanceSearcher<'bump> for EufCmaMac<'bump> {
    fn search_instances(&self, str: &str, env:&Environement<'bump>) -> Vec<RichFormula<'bump>> {
        todo!()
    }
}
impl<'bump> InstanceSearcher<'bump> for EufCmaSign<'bump> {
    fn search_instances(&self, str: &str, env:&Environement<'bump>) -> Vec<RichFormula<'bump>> {
        todo!()
    }
}
impl<'bump> InstanceSearcher<'bump> for IntCtxt<'bump> {
    fn search_instances(&self, str: &str, env:&Environement<'bump>) -> Vec<RichFormula<'bump>> {
        todo!()
    }
}
