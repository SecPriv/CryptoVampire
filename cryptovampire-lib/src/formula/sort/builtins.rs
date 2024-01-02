use static_init::dynamic;

use super::{
    inner::{Other, TermBase},
    new_static_sort, InnerSort, Sort,
};

#[dynamic]
pub static BOOL: Sort<'static> = new_static_sort(InnerSort::Base(TermBase::Bool));
#[dynamic]
pub static CONDITION: Sort<'static> = new_static_sort(InnerSort::Base(TermBase::Condition));
#[dynamic]
pub static STEP: Sort<'static> = new_static_sort(InnerSort::Other(Other::Step));
#[dynamic]
pub static BITSTRING: Sort<'static> = new_static_sort(InnerSort::Base(TermBase::Bitstring));
#[dynamic]
pub static MESSAGE: Sort<'static> = new_static_sort(InnerSort::Base(TermBase::Message));
#[dynamic]
pub static NAME: Sort<'static> = new_static_sort(InnerSort::Other(Other::Name));

#[dynamic]
pub static BUILT_IN_SORTS: [Sort<'static>; 6] = [
    BOOL.clone(),
    CONDITION.clone(),
    MESSAGE.clone(),
    BITSTRING.clone(),
    STEP.clone(),
    NAME.clone(),
];

// alias
#[dynamic]
pub static TIME: Sort<'static> = STEP.clone();
