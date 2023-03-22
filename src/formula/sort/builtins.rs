use static_init::dynamic;

use super::{new_static_sort, Sort};

#[dynamic]
pub static BOOL: StatSort = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "bool",
    Default::default(),
);
#[dynamic]
pub static CONDITION: StatSort = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Condition",
    Default::default(),
);
#[dynamic]
pub static STEP: StatSort = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Time",
    Default::default(),
);
#[dynamic]
pub static MESSAGE: StatSort = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Message",
    Default::default(),
);
#[dynamic]
pub static NONCE: StatSort = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Nonce",
    Default::default(),
);

pub type StatSort = Sort<'static>;
