use cryptovampire_lib::{
    environement::environement::Environement,
    formula::{formula::{ARichFormula, RichFormula}, function, sort::builtins::MESSAGE},
    problem::crypto_assumptions::{CryptoAssumption, EufCmaMac, EufCmaSign, IntCtxt},
};
use itertools::Itertools;
use regex::Regex;

use crate::runner::tmpformula::TmpFormula;

pub trait InstanceSearcher<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>>;
}

impl<'bump> InstanceSearcher<'bump> for CryptoAssumption<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>> {
        match self {
            CryptoAssumption::EufCmaMac(a) => a.search_instances(str, env),
            CryptoAssumption::EufCmaSign(a) => a.search_instances(str, env),
            CryptoAssumption::IntCtxtSenc(a) => a.search_instances(str, env),
            CryptoAssumption::Nonce(_) | CryptoAssumption::MemoryCell(_) => vec![],
        }
    }
}

impl<'bump> InstanceSearcher<'bump> for EufCmaMac<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>> {
        // TODO: add support for eq

        let re = Regex::new(&format!("{:}", self.verify.name())).unwrap();

        let mut out = vec![];
        let functions = env.get_function_hash();

        out.extend(re.find_iter(str).filter_map(|m| {
            TmpFormula::parse(&str[m.start()..]).and_then(|tmp| {
                let mut vars = Default::default();
                tmp.to_rich_formula(&functions, MESSAGE.as_sort().into(), &mut vars)
                    .ok()
            })
        }).map_into());
        out
    }
}
impl<'bump> InstanceSearcher<'bump> for EufCmaSign<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>> {
        let re = Regex::new(&format!("{:}", self.verify.name())).unwrap();

        let mut out = vec![];
        let functions = env.get_function_hash();

        out.extend(re.find_iter(str).filter_map(|m| {
            TmpFormula::parse(&str[m.start()..]).and_then(|tmp| {
                let mut vars = Default::default();
                tmp.to_rich_formula(&functions, MESSAGE.as_sort().into(), &mut vars)
                    .ok()
            })
        }).map_into());

        out
    }
}
impl<'bump> InstanceSearcher<'bump> for IntCtxt<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>> {
        todo!()
    }
}
