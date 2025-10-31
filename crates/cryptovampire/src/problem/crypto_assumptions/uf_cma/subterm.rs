use std::hash::Hash;
use std::sync::Arc;

use if_chain::if_chain;
use itertools::chain;
use utils::arc_into_iter::ArcIntoIter;

use super::UfCma;
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::function::Function;
use crate::formula::function::builtin::{EQUALITY, EQUALITY_TA};
use crate::formula::function::name_caster_collection::NameCasterCollection;
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::{MESSAGE, NAME};
use crate::subterm::traits::{SubtermAux, VarSubtermResult};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAux<'bump> {
    uf_cma: UfCma<'bump>,
    name_caster: Arc<NameCasterCollection<'bump>>,
}

impl<'bump> KeyAux<'bump> {
    pub fn new(uf_cma: UfCma<'bump>, name_caster: Arc<NameCasterCollection<'bump>>) -> Self {
        Self {
            uf_cma,
            name_caster,
        }
    }
}

impl<'bump> SubtermAux<'bump> for KeyAux<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    fn sort(&self) -> Sort<'bump> {
        *NAME
    }

    fn var_eval_and_next(
        &self,
        m: &ARichFormula<'bump>,
    ) -> VarSubtermResult<'bump, Self::IntoIter> {
        let nexts = match m.as_ref() {
            RichFormula::Fun(fun, args) => 'function: {
                if_chain! {
                    if fun == &self.uf_cma.mac;
                    if let RichFormula::Fun(nf, _args2) = args[1].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args2[0]])
                        break 'function [args[0].clone()].into()
                    }
                }
                if_chain! {
                    if fun == &self.uf_cma.verify;
                    if let RichFormula::Fun(nf, _args2) = args[2].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args[1], &args2[0]])
                        break 'function [args[0].clone(), args[1].clone()].into()
                    }
                }
                ArcIntoIter::from(args)
            }
            RichFormula::Quantifier(_, arg) => [arg.shallow_copy()].into(),
            _ => [].into(),
        };

        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: m_sort.is_err() || self.sort() == m_sort.unwrap(),
            nexts,
        }
    }
}

impl<'bump> PartialOrd for KeyAux<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(&self, &other))
    }
}
impl<'bump> Ord for KeyAux<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.uf_cma, &other.uf_cma).then_with(|| {
            Ord::cmp(
                &Arc::as_ptr(&self.name_caster),
                &Arc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for KeyAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.uf_cma.hash(state);
        self.name_caster.hash(state);
    }
}

/// We can ignore verifies, hence this complexifies the search
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct UfCmaMainSubtAux<'bump> {
    uf_cma: UfCma<'bump>,
}

impl<'bump> SubtermAux<'bump> for UfCmaMainSubtAux<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    fn sort(&self) -> Sort<'bump> {
        *MESSAGE
    }

    fn var_eval_and_next(
        &self,
        m: &ARichFormula<'bump>,
    ) -> VarSubtermResult<'bump, Self::IntoIter> {
        let nexts = match m.as_ref() {
            RichFormula::Fun(f, args) => self.var_eval_and_next_fun(*f, Arc::clone(args)),
            RichFormula::Quantifier(_, arg) => [arg.shallow_copy()].into(),
            _ => [].into(),
        };

        let x_sort = self.sort();
        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: m_sort.map(|m_sort| x_sort == m_sort).unwrap_or(true), /* m_sort.is_err() || x_sort == m_sort.unwrap(), */
            nexts,
        }
    }
}

impl<'bump> UfCmaMainSubtAux<'bump> {
    pub fn new(uf_cma: UfCma<'bump>) -> Self {
        Self { uf_cma }
    }

    fn var_eval_and_next_fun(
        &self,
        f: Function<'bump>,
        args: Arc<[ARichFormula<'bump>]>,
    ) -> <Self as SubtermAux<'bump>>::IntoIter {
        let uf_cma = self.uf_cma();

        if_chain! { // verify
            if f == uf_cma.verify();
            if let [sig, message, key] = args.as_ref();
            if let RichFormula::Fun(m_mac, m_args) = sig.as_ref();
            if *m_mac == uf_cma.mac();
            then {
                return chain!([message, key], m_args.as_ref().iter()).cloned().collect()
            }
        }

        if_chain! { // in case of equality
            if uf_cma.is_hmac();
            if f == *EQUALITY || f == *EQUALITY_TA;
            if let [left, right] = args.as_ref();
            then {
                let mut nexts = Vec::with_capacity(2*4);
                for e in [left, right] {
                    if_chain!{
                        if let RichFormula::Fun(m_mac, m_args) = e.as_ref();
                        if *m_mac == uf_cma.mac();
                        then {
                            debug_assert_eq!(m_args.len(), 2); // should be ensured by the *m_mac == uf_cma.mac() check
                            nexts.extend(m_args.iter().cloned())
                        }
                    }
                }

                if !nexts.is_empty() {
                    return nexts.into_iter().collect()
                }
             }
        }

        args.into()
    }

    pub fn uf_cma(&self) -> UfCma<'bump> {
        self.uf_cma
    }
}
