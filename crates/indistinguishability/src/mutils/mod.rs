// pub mod linked_list;

mod bag {
    use std::{rc::Rc, slice::Iter};

    use utils::implvec;

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct InnerBag<U> {
        top: Vec<U>,
        lower: Vec<Bag<U>>,
    }

    #[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Bag<U>(Rc<InnerBag<U>>);

    impl<U> Clone for Bag<U> {
        fn clone(&self) -> Self {
            Self(Rc::clone(&self.0))
        }
    }

    #[derive(Debug, Default, Clone)]
    struct BagIter<'a, U> {
        current: Iter<'a, U>,
        pile: Vec<&'a Bag<U>>,
    }

    impl<'a, U> Iterator for BagIter<'a, U> {
        type Item = &'a U;

        fn next(&mut self) -> Option<Self::Item> {
            let BagIter { current, pile } = self;
            match current.next() {
                Some(x) => Some(x),
                None => {
                    let nxt_bag = pile.pop()?;
                    let InnerBag { top, lower } = nxt_bag.0.as_ref();
                    *current = top.iter();
                    pile.extend(lower.iter());
                    self.next()
                }
            }
        }
    }

    impl<U> Bag<U> {
        pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a U> {
            BagIter {
                current: self.0.top.iter(),
                pile: self.0.lower.iter().collect(),
            }
        }

        pub fn new(top: implvec!(U), lower: implvec!(Self)) -> Self {
            Bag(Rc::new(InnerBag {
                top: top.into_iter().collect(),
                lower: lower.into_iter().collect(),
            }))
        }
    }

    impl<U> FromIterator<U> for Bag<U> {
        fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
            Bag::new(iter, [])
        }
    }

    impl<U> FromIterator<Bag<U>> for Bag<U> {
        fn from_iter<T: IntoIterator<Item = Bag<U>>>(iter: T) -> Self {
            Bag::new([], iter)
        }
    }
}
pub use bag::Bag;
