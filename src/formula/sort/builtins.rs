use static_init::dynamic;

use super::{new_static_sort, Sort};

#[dynamic]
pub static BOOL: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "bool",
    Default::default(),
    None,
);
#[dynamic]
pub static CONDITION: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Condition",
    Default::default(),
    Some(BOOL.clone()),
);
#[dynamic]
pub static STEP: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Time",
    Default::default(),
    None,
);
#[dynamic]
pub static BITSTRING: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Bitstring",
    Default::default(),
    None,
);
#[dynamic]
pub static MESSAGE: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Message",
    Default::default(),
    Some(BITSTRING.clone()),
);
#[dynamic]
pub static NONCE: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Nonce",
    Default::default(),
    None,
);

#[dynamic]
pub static NAME: Sort<'static> = new_static_sort(
    /* STATIC_ALLOCATOR.as_ref(), */ "Name",
    Default::default(),
    None,
);

// pub type StatSort = Sort<'static>;
