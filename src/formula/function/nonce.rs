use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Nonce<'bump> {
    args: Box<[Sort<'bump>]>,
    name: Box<str>,
}

fn enlarge<'a, 'b>(q: Nonce<'a>) -> Nonce<'b> where 'a:'b {
    q
}