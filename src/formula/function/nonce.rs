use bumpalo::boxed::Box;

use crate::formula::sort::Sort;


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Nonce<'bump> {
    args: Box<'bump, [Sort<'bump>]>,
    name: Box<'bump, str>
}