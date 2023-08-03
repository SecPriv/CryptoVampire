use std::{convert::Infallible, error::Error, ptr::NonNull};

use itertools::Itertools;

use crate::utils::{
    precise_as_ref::PreciseAsRef,
    utils::{AccessToInvalidData, AlreadyInitialized, MaybeInvalid},
};

use super::allocator::{Container, ContainerTools};

// pub type RefPointee<'bump, R> = Option<<R as Reference<'bump>>::Inner<'bump>>;
// pub type RefInner<'bump, R> = <R as Reference<'bump>>::Inner<'bump>;

///
/// # Safety
/// No access to invalid data as defined by [MaybeInvalid]
pub trait Reference<'bump> : Sized + 'bump {
    // type Inner<'a> where 'a:'bump, Self:'a;
    type Inner<'a> where 'a:'bump, Self:'a;

    fn from_ref(ptr: &'bump Option<Self::Inner<'bump>>) -> Self;
    fn to_ref(&self) -> &'bump Option<Self::Inner<'bump>>;

    fn new_uninit<C>(container: &'bump C) -> Self
    where
        C: Container<'bump, Self>,
    {
        Self::from_ref(container.allocate_uninit())
    }

    fn new_from<C>(container: &'bump C, content: Self::Inner<'bump>) -> Self
    where
        C: Container<'bump, Self>,
    {
        Self::from_ref(container.allocate_inner(content))
    }

    // fn try_alloc_array_cyclic_with_residual<C, F, T, E1, E2, const N: usize>(
    //     container: &'bump C,
    //     f: F,
    // ) -> Result<(T, [Self; N]), E2>
    // where
    //     C: Container<'bump, Self>,
    //     F: for<'a> FnOnce(&'a [Self; N]) -> Result<(T, [Self::Inner; N]), E1>,
    //     E1: Error,
    //     E2: Error + From<E1> + From<AlreadyInitialized>,
    // {
    //     container.try_alloc_array_cyclic_with_residual(f)
    // }


    fn maybe_precise_as_ref(&self) -> Result<&'bump Self::Inner<'bump>, AccessToInvalidData> {
        self.to_ref().as_ref().ok_or(AccessToInvalidData::Error)
    }

    /// initialize via inner mutability
    unsafe fn initialize_with(&self, content: Self::Inner<'bump>) -> Result<&Self, AlreadyInitialized> {
        if !self.is_valid() {
            let ptr = self.to_ref() as *const _ as *mut Option<Self::Inner<'bump>>;
            core::ptr::drop_in_place(ptr);
            core::ptr::write(ptr, Some(content));
            Ok(self)
        } else {
            Err(AlreadyInitialized::Error)
        }
    }

    fn as_inner(&self) -> &Self::Inner<'bump> {
        self.precise_as_ref()
    }
}

impl<'bump, R> PreciseAsRef<'bump, R::Inner<'bump>> for R
where
    R: Reference<'bump>,
{
    fn precise_as_ref(&self) -> &'bump R::Inner<'bump> {
        self.maybe_precise_as_ref().unwrap()
    }
}

impl<'bump, T> MaybeInvalid for T
where
    T: Reference<'bump>,
{
    fn is_valid(&self) -> bool {
        self.maybe_precise_as_ref().is_ok()
    }
}
// impl<'bump, R> From<&'bump RefPointee<'bump, R>> for R
// where
//     R: Reference<'bump>,
// {
//     fn from(value: &'bump R::Inner) -> Self {
//         Self::from_ref(value)
//     }
// }
