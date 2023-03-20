use static_init::dynamic;

use super::RcSort;

#[dynamic]
pub static BOOL: RcSort = RcSort::new("Bool".to_owned(), Default::default());

#[dynamic]
pub static CONDITION: RcSort = RcSort::new("Conditon".to_owned(), Default::default());

#[dynamic]
pub static MESSAGE: RcSort = RcSort::new("Message".to_owned(), Default::default());

#[dynamic]
pub static STEP: RcSort = RcSort::new("Time".to_owned(), Default::default());

#[dynamic]
pub static NONE: RcSort = RcSort::new("Nonce".to_owned(), Default::default());
