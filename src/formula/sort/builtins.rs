use static_init::dynamic;

use crate::formula::static_allocator::STATIC_ALLOCATOR;

use super::{InnerSort, Sort};

#[dynamic]
pub static BOOL: StatSort =
    InnerSort::new(STATIC_ALLOCATOR.as_ref(), "bool", Default::default()).as_sort();
#[dynamic]
pub static CONDITION: StatSort =
    InnerSort::new(STATIC_ALLOCATOR.as_ref(), "Condition", Default::default()).as_sort();
#[dynamic]
pub static STEP: StatSort =
    InnerSort::new(STATIC_ALLOCATOR.as_ref(), "Time", Default::default()).as_sort();
#[dynamic]
pub static MESSAGE: StatSort =
    InnerSort::new(STATIC_ALLOCATOR.as_ref(), "Message", Default::default()).as_sort();
#[dynamic]
pub static NONCE: StatSort =
    InnerSort::new(STATIC_ALLOCATOR.as_ref(), "Nonce", Default::default()).as_sort();

pub type StatSort = Sort<'static>;
