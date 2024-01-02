use cryptovampire_lib::formula::function::builtin::*;
use utils::maybe_owned::MOw;

use super::super::parsing_environement::FunctionCache;

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn NOT_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(NOT_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn NOT_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(NOT.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn EQUALITY_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(EQUALITY.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn EQUALITY_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(EQUALITY_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn IFF_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(IFF.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn IMPLIES_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(IMPLIES.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn IMPLIES_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(IMPLIES_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn AND_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(AND_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn AND_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(AND.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn OR_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(OR_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn OR_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(OR.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn TRUE_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(TRUE_F_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn TRUE_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(TRUE_F.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn FALSE_TA_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(FALSE_F_TA.clone().into())
}

// #[dynamic]
#[allow(non_snake_case)]
pub(crate) fn FALSE_CACHE<'a, 'str, 'bump>() -> MOw<'a, FunctionCache<'str, 'bump>> {
    MOw::Owned(FALSE_F.clone().into())
}
