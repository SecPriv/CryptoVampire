//! Things that look for instance in solvers ouputs

use itertools::Itertools;
use log::{debug, trace};
use regex::Regex;
use static_init::dynamic;

use super::tptp::TptpParse;
use super::{Runner, VampireExec};
use crate::environement::environement::Environement;
use crate::formula::TmpFormula;
use crate::formula::formula::ARichFormula;
use crate::formula::sort::builtins::BOOL;
use crate::formula::sort::sort_proxy::SortProxy;
use crate::problem::crypto_assumptions::{CryptoAssumption, EufCma, IntCtxt, UfCma};

#[dynamic]
static EXTRACT_FORMULA: Regex = Regex::new(r"\[SA\] new: \d*?\. (.*?) \[.*?\]").unwrap();

pub trait InstanceSearcher<'bump, R: Runner> {
    /// Build a list of formulas that might be usefull to find instance of [Self] in the output of [R].
    ///
    /// ## args
    /// - **str**: the output of [R]
    /// - **env**: the environement
    fn search_instances(
        &self,
        str: &R::TimeoutR,
        env: &Environement<'bump>,
    ) -> Vec<ARichFormula<'bump>>;
}

impl<'bump> InstanceSearcher<'bump, VampireExec> for CryptoAssumption<'bump> {
    fn search_instances(
        &self,
        str: &<VampireExec as Runner>::TimeoutR,
        env: &Environement<'bump>,
    ) -> Vec<ARichFormula<'bump>> {
        match self {
            CryptoAssumption::UfCma(a) => a.search_instances(str, env),
            CryptoAssumption::EufCmaSign(a) => a.search_instances(str, env),
            CryptoAssumption::IntCtxtSenc(a) => a.search_instances(str, env),
            CryptoAssumption::Nonce(_)
            | CryptoAssumption::MemoryCell(_)
            | CryptoAssumption::Unfolding(_) => vec![],
        }
    }
}

impl<'bump> InstanceSearcher<'bump, VampireExec> for UfCma<'bump> {
    fn search_instances(
        &self,
        str: &<VampireExec as Runner>::TimeoutR,
        env: &Environement<'bump>,
    ) -> Vec<ARichFormula<'bump>> {
        let macname = self.mac().name();
        let verifyname = self.verify().name();
        let functions = env.get_function_hash();
        let _bool = SortProxy::from(BOOL.as_sort());

        EXTRACT_FORMULA
            .captures_iter(str)
            .map(|c| {
                trace!("new clause {:?}", &c);
                c.extract()
            })
            .flat_map(|(_, [content])| content.split("|"))
            .filter(|s| s.contains(macname.as_ref()) || s.contains(verifyname.as_ref()))
            .inspect(|s| {
                debug!("new potential instance {:?}", s);
            })
            .filter_map(|s| match TmpFormula::parse(s) {
                Ok(f) => Some((s, f)),
                Err(e) => {
                    debug!("{s} failed ({e:?})");
                    None
                }
            })
            .filter_map(|(s, f)| {
                f.to_rich_formula(&functions, Default::default(), &mut Default::default())
                    .ok()
                    .map(|f| (s, f))
            })
            .map(|(s, f)| {
                debug!("found {} from {}", f, s);
                f
            })
            .map_into()
            .collect()
    }
}
impl<'bump> InstanceSearcher<'bump, VampireExec> for EufCma<'bump> {
    fn search_instances(
        &self,
        str: &<VampireExec as Runner>::TimeoutR,
        env: &Environement<'bump>,
    ) -> Vec<ARichFormula<'bump>> {
        let signname = self.sign.name();
        let verifyname = self.verify.name();
        let functions = env.get_function_hash();

        if cfg!(debug_assertions) {
            debug!(
                "saved functions [{}]",
                functions.keys().map(|f| f.as_ref().to_string()).join(", ")
            )
        }

        // let bool = SortProxy::from(BOOL.as_sort());
        EXTRACT_FORMULA
            .captures_iter(str)
            .map(|c| {
                // debug!("found {:?}", &c);
                c.extract()
            })
            .flat_map(|(_, [content])| content.split("|"))
            .filter(|s| s.contains(signname.as_ref()) || s.contains(verifyname.as_ref()))
            .inspect(|s| debug!("new potential instance {:?}", &s))
            .filter_map(|s| match TmpFormula::parse(s) {
                Ok(f) => Some((s, f)),
                Err(_) => {
                    debug!("{s} failed");
                    None
                }
            })
            .filter_map(|(s, f)| {
                f.to_rich_formula(&functions, Default::default(), &mut Default::default())
                    .ok()
                    .map(|f| (s, f))
            })
            .map(|(s, f)| {
                debug!("found {} from {}", f, s);
                f
            })
            .map_into()
            .collect()
    }
}
impl<'bump> InstanceSearcher<'bump, VampireExec> for IntCtxt<'bump> {
    fn search_instances(
        &self,
        str: &<VampireExec as Runner>::TimeoutR,
        env: &Environement<'bump>,
    ) -> Vec<ARichFormula<'bump>> {
        let dec = self.dec.name();
        let functions = env.get_function_hash();

        EXTRACT_FORMULA
            .captures_iter(str)
            .map(|c| {
                // debug!("found {:?}", &c);
                c.extract()
            })
            .flat_map(|(_, [content])| content.split("|"))
            .filter(|s| s.contains(dec.as_ref()))
            .inspect(|s| {
                debug!("new potential instance {:?}", s);
            })
            .filter_map(|s| match TmpFormula::parse(s) {
                Ok(f) => Some((s, f)),
                Err(_) => {
                    debug!("{s} failed");
                    None
                }
            })
            .filter_map(|(s, f)| {
                f.to_rich_formula(&functions, Default::default(), &mut Default::default())
                    .ok()
                    .map(|f| (s, f))
            })
            .map(|(s, f)| {
                debug!("found {} from {}", f, s);
                f
            })
            .map_into()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::runner::searcher::EXTRACT_FORMULA;

    #[test]
    fn regexp_test() {
        let tests = [
            "[SA] new: 4640. ($true = X3) | 'ta$iff'(X1,X0) | (X2 = X3) | (X3 = X4) | ($false = \
             X4) <- (~3, 8, 15) [backward demodulation 4444,4607]",
            "[SA] new: 4641. ~'Condition$_13$subterm_nonce'(X0,$true) | \
             'Message$_13$subterm_nonce'(X0,X1) | 'Message$_13$subterm_nonce'(X0,X2) | \
             'Message$_13$subterm_nonce'(X0,X3) <- (~3, 8, 15) [backward demodulation 434,4607]",
            "[SA] new: 4287. (X1 != X1) | (X0 = X1) | (X0 = X0) | (X1 = X2) | ($false = X2) \
             [equality factoring 976]",
            "[SA] new: 4640. ($true = X3) | 'ta$iff'(X1,X0) | (X2 = X3) | (X3 = X4) | ($false = \
             X4) <- (~3, 8, 15) [backward demodulation 4444,4607]
[SA] new: 4641. ~'Condition$_13$subterm_nonce'(X0,$true) | 'Message$_13$subterm_nonce'(X0,X1) | \
             'Message$_13$subterm_nonce'(X0,X2) | 'Message$_13$subterm_nonce'(X0,X3) <- (~3, 8, \
             15) [backward demodulation 434,4607]",
        ];

        assert!(tests.iter().all(|s| EXTRACT_FORMULA.is_match(s)))
    }
}
