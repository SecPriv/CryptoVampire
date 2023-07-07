use std::{ops::{Deref, DerefMut}, cell::Ref};

#[inline(always)]
pub fn replace_if_eq<T: Eq>(a: T, b: T, c: T) -> T {
    if a == b {
        c
    } else {
        a
    }
}

pub fn clone_iter<'a, E, I>(iter: I) -> impl Iterator<Item = E> + 'a
where
    E: Clone + 'a,
    I: Iterator<Item = &'a E> + 'a,
{
    iter.map(|e| e.clone())
}

pub struct StackBox<T>(T);

impl<T> StackBox<T> {
    pub fn new(t: T) -> Self {
        StackBox(t)
    }
}

impl<T> Deref for StackBox<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for StackBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub(crate) fn reset_vec<'a, 'b, T>(v: &'a mut Vec<*const T>) -> &'a mut Vec<&'b T> {
    v.clear();
    unsafe { std::mem::transmute(v) }
}

pub(crate) fn transpose<A: Eq + Clone, B: Eq>(vec: Vec<(A, Vec<B>)>) -> Vec<(B, Vec<A>)> {
    let mut result = vec![];

    for (a, v) in vec {
        for b in v {
            let i = result
                .iter()
                .position(|(b2, _)| b2 == &b)
                .unwrap_or_else(|| {
                    let i = result.len();
                    result.push((b, vec![]));
                    i
                });
            let bvec = &mut result[i].1;
            if !bvec.contains(&a) {
                bvec.push(a.clone())
            }
        }
    }
    result
}

pub fn repeat_n_zip<P, I, T>(p: P, iter: I) -> impl Iterator<Item = (P, T)>
where
    P: Clone,
    I: IntoIterator<Item = T>,
{
    // std::iter::repeat(p).zip(iter.into_iter())
    iter.into_iter().map(move |t| (p.clone(), t))
}

#[macro_export]
macro_rules! implderef {
    ($b:lifetime, $t:ty) => {
        impl core::ops::Deref<Target = $t> + $b
    };
    ($t:ty) => {
        impl core::ops::Deref<Target = $t>
    };
}

#[macro_export]
macro_rules! implvec {
    ($t:ty) => {
        impl std::iter::IntoIterator<Item = $t>
    };

}

#[macro_export]
macro_rules! destvec {
    ([$($arg:ident),*] = $vec:expr) => {
        destvec!{ [$($arg),*] = $vec; |err| {
            panic!("{}", err);
        }}
    };

    ([$($arg:ident),*] = $vec:expr; |$err:ident| $err_handling:block) => {
        let mut iter = $vec.into_iter();
        $(
            let $arg = if let Some(tmp) = iter.next() {
                tmp
            } else {
                {
                    let $err = "not enough elements";
                    $err_handling
                }
            };
        )*
        if !iter.next().is_none() {
            {
                let $err = "too many elements";
                $err_handling
            }
        }
    }
}