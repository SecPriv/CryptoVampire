use cryptovampire_lib::{
    environement::environement::Environement,
    formula::{
        formula::{ARichFormula, RichFormula},
        function,
        sort::{
            builtins::{BOOL, MESSAGE},
            sort_proxy::SortProxy,
        },
    },
    problem::crypto_assumptions::{CryptoAssumption, EufCmaMac, EufCmaSign, IntCtxt},
};
use itertools::Itertools;
use regex::Regex;
use static_init::dynamic;

use crate::runner::tmpformula::TmpFormula;

#[dynamic]
static EXTRACT_FORMULA: Regex = Regex::new(r"\[SA\] new: \d*?\. (.*?) \[.*?\]").unwrap();

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
        let macname = self.mac.name();
        let verifyname = self.verify.name();
        let functions = env.get_function_hash();
        let bool = SortProxy::from(BOOL.as_sort());
        EXTRACT_FORMULA
            .captures_iter(str)
            .map(|c| c.extract())
            .flat_map(|(_, [content])| content.split("|"))
            .filter(|s| s.contains(macname.as_ref()) || s.contains(verifyname.as_ref()))
            .filter_map(|s| TmpFormula::parse(s).ok())
            .filter_map(|f| {
                f.to_rich_formula(&functions, bool.clone(), &mut Default::default())
                    .ok()
            })
            .map_into()
            .collect()
    }
}
impl<'bump> InstanceSearcher<'bump> for EufCmaSign<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>> {
        let signname = self.sign.name();
        let verifyname = self.verify.name();
        let functions = env.get_function_hash();
        let bool = SortProxy::from(BOOL.as_sort());
        EXTRACT_FORMULA
            .captures_iter(str)
            .map(|c| c.extract())
            .flat_map(|(_, [content])| content.split("|"))
            .filter(|s| s.contains(signname.as_ref()) || s.contains(verifyname.as_ref()))
            .filter_map(|s| TmpFormula::parse(s).ok())
            .filter_map(|f| {
                f.to_rich_formula(&functions, bool.clone(), &mut Default::default())
                    .ok()
            })
            .map_into()
            .collect()
    }
}
impl<'bump> InstanceSearcher<'bump> for IntCtxt<'bump> {
    fn search_instances(&self, str: &str, env: &Environement<'bump>) -> Vec<ARichFormula<'bump>> {
        todo!()
    }
}
