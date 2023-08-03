use std::ptr::NonNull;

use itertools::Itertools;

use crate::utils::{
    precise_as_ref::PreciseAsRef,
    utils::{AccessToInvalidData, AlreadyInitialized, MaybeInvalid},
};

use super::allocator::Container;

pub type RefPointee<'bump, R> = Option<<R as Reference<'bump>>::Inner>;

///
/// # Safety
/// No access to invalid data
pub trait Reference<'bump>: AsRef<RefPointee<'bump, Self>> {
    type Inner;

    fn from_ref(ptr: &'bump RefPointee<'bump, Self>) -> Self;

    fn new_uninit<C>(container: &C) -> Self
    where
        C: Container<'bump, Self>,
    {
        container.allocate_uninit()
    }

    fn new_from<C>(container: &C, content: Self::Inner) -> Self
    where
        C: Container<'bump, Self>,
    {
        container.allocate(content)
    }

    fn new_with_array<C, F, const N: usize>(
        container: &C,
        f: F,
    ) -> Result<[Self; N], AlreadyInitialized>
    where
        C: Container<'bump, Self>,
        F: for<'a> FnOnce(&'a [Self; N]) -> [Self::Inner; N],
    {
        // let uninit = Self::new_uninit(container);
        let uninits = std::array::from_fn(|_| Self::new_uninit(container));
        let values = f(&uninits);
        // uninit.initialize_with(value).map(|_| uninit)
        values
            .into_iter()
            .zip_eq(uninits.iter())
            .try_for_each(|(content, uninit)| uninit.initialize_with(content))?;
        uninits
    }

    fn new_with<C, F>(container: &C, f: F) -> Result<Self, AlreadyInitialized>
    where
        C: Container<'bump>,
        F: for<'a> FnOnce(&'a Self) -> Self::Inner,
    {
        Self::new_with_array(container, |[u]| [f(u)])
    }

    fn maybe_precise_as_ref(&self) -> Result<&'bump Self::Inner, AccessToInvalidData> {
        self.as_ref().as_ref().ok_or(AccessToInvalidData::Error)
    }

    /// initialize via inner mutability
    unsafe fn initialize_with(&self, content: Self::Inner) -> Result<&Self, AlreadyInitialized> {
        if !self.is_valid() {
            let ptr = self.as_ref() as *const _ as *mut RefPointee<'bump, Self>;
            core::ptr::drop_in_place(ptr);
            core::ptr::write(ptr, Some(content));
            Ok(self)
        } else {
            Err(AlreadyInitialized::Error)
        }
    }
}

impl<'bump, R> PreciseAsRef<'bump, R::Inner> for R
where
    R: Reference<'bump>,
{
    fn precise_as_ref(&self) -> &'bump R::Inner {
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
