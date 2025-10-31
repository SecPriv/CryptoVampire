use utils::maybe_owned::MOw;

use super::super::parsing_environement::FunctionCache;
use crate::formula::function::builtin::*;

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn NOT_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*NOT_TA).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn NOT_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*NOT).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn EQUALITY_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*EQUALITY).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn EQUALITY_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*EQUALITY_TA).into())
}

// #[dynamic]
// #[allow(non_snake_case)]
// pub(crate) fn IFF_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
//     MOw::Owned(IFF.clone().into())
// }

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn IMPLIES_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*IMPLIES).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn IMPLIES_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*IMPLIES_TA).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn AND_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*AND_TA).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn AND_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*AND).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn OR_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*OR_TA).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn OR_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*OR).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn TRUE_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*TRUE_F_TA).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn TRUE_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*TRUE_F).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn FALSE_TA_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*FALSE_F_TA).into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn FALSE_CACHE<'a, 'str, 'bump, S>() -> MOw<'a, FunctionCache<'str, 'bump, S>> {
    MOw::Owned((*FALSE_F).into())
}
