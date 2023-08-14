use crate::formula::function::builtin::*;

use super::super::parsing_environement::FunctionCache;

use static_init::dynamic;

#[dynamic]
pub(crate) static NOT_TA_CACHE: FunctionCache<'static, 'static> = NOT_TA.clone().into();

#[dynamic]
pub(crate) static NOT_CACHE: FunctionCache<'static, 'static> = NOT.clone().into();

#[dynamic]
pub(crate) static EQUALITY_CACHE: FunctionCache<'static, 'static> = EQUALITY.clone().into();

#[dynamic]
pub(crate) static EQUALITY_TA_CACHE: FunctionCache<'static, 'static> = EQUALITY_TA.clone().into();

#[dynamic]
pub(crate) static IFF_CACHE: FunctionCache<'static, 'static> = IFF.clone().into();

#[dynamic]
pub(crate) static IMPLIES_CACHE: FunctionCache<'static, 'static> = IMPLIES.clone().into();

#[dynamic]
pub(crate) static IMPLIES_TA_CACHE: FunctionCache<'static, 'static> = IMPLIES_TA.clone().into();

#[dynamic]
pub(crate) static AND_TA_CACHE: FunctionCache<'static, 'static> = AND_TA.clone().into();

#[dynamic]
pub(crate) static AND_CACHE: FunctionCache<'static, 'static> = AND.clone().into();

#[dynamic]
pub(crate) static OR_TA_CACHE: FunctionCache<'static, 'static> = OR_TA.clone().into();

#[dynamic]
pub(crate) static OR_CACHE: FunctionCache<'static, 'static> = OR.clone().into();

#[dynamic]
pub(crate) static TRUE_TA_CACHE: FunctionCache<'static, 'static> = TRUE_F_TA.clone().into();

#[dynamic]
pub(crate) static TRUE_CACHE: FunctionCache<'static, 'static> = TRUE_F.clone().into();

#[dynamic]
pub(crate) static FALSE_TA_CACHE: FunctionCache<'static, 'static> = FALSE_F_TA.clone().into();

#[dynamic]
pub(crate) static FALSE_CACHE: FunctionCache<'static, 'static> = FALSE_F.clone().into();
