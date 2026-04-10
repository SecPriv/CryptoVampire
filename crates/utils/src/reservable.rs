use std::collections::VecDeque;
use std::hash::{BuildHasher, Hash};

use hashbrown::{HashMap, HashSet};

pub trait Reservable {
    fn gen_reserve(&mut self, size: usize);
}

macro_rules! impl_reservable {
    (impl <$($gen:tt),*> for $t:ty $(where $($bounds:tt)*)?) => {
        impl <$($gen),*> Reservable for $t $(where $($bounds)*)? {
            fn gen_reserve(&mut self, size: usize) {
              Self::reserve(self, size)
            }
        }
    };

    (impl for $t:ty $(where $($bounds:tt)*)?) => {
        impl Reservable for $t $(where $($bounds)*)? {
            fn gen_reserve(&mut self, size: usize) {
                self.reserve(size);
            }
        }
    };
}
impl_reservable!(impl <U> for Vec<U>);
impl_reservable!(impl <U> for VecDeque<U>);
impl_reservable!(impl <K, V, S> for HashMap<K, V, S> where K : Eq + Hash, S: BuildHasher);
impl_reservable!(impl <K, S> for HashSet<K, S> where K : Eq + Hash, S: BuildHasher);
