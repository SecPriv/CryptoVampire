use std::marker::PhantomData;
use std::ptr::NonNull;

use utils::utils::{AccessToInvalidData, AlreadyInitialized};

use super::allocator::Container;
use super::reference::Reference;

pub trait Containable<'bump> {}

#[allow(clippy::missing_safety_doc)] // FIXME
pub trait Contained<'bump>: 'bump + Sized + std::fmt::Debug {
    type Pointer<'a>: Sized
    where
        'bump: 'a;

    fn ptr_from_raw<'a>(
        ptr: NonNull<Option<Self>>,
        lt: PhantomData<&'bump Option<Self>>,
    ) -> Self::Pointer<'a>
    where
        'bump: 'a;

    fn ptr_to_raw(ptr: &Self::Pointer<'bump>) -> NonNull<Option<Self>>;

    fn ptr_to_ref<'a>(ptr: &Self::Pointer<'bump>) -> &'a Option<Self>
    where
        'bump: 'a,
    {
        unsafe { Self::ptr_to_raw(ptr).as_ref() }
    }

    fn new_ptr_uninit<'a, C>(container: &'bump C) -> Self::Pointer<'a>
    where
        C: Container<'bump, Self>,
        'bump: 'a,
    {
        Self::ptr_from_raw(container.allocate_uninit(), Default::default())
    }

    fn new_ptr_from_inner<'a, C>(container: &'bump C, content: Self) -> Self::Pointer<'a>
    where
        C: Container<'bump, Self>,
        'bump: 'a,
    {
        Self::ptr_from_raw(container.allocate_inner(content), Default::default())
    }

    fn maybe_precise_as_ref(
        ptr: &Self::Pointer<'bump>,
    ) -> Result<&'bump Self, AccessToInvalidData> {
        // self.to_ref().as_ref().ok_or(AccessToInvalidData::Error)
        Self::ptr_to_ref(ptr)
            .as_ref()
            .ok_or(AccessToInvalidData::Error)
    }

    /// initialize via inner mutability
    unsafe fn initialize_with<'b>(
        ptr: &'b Self::Pointer<'bump>,
        content: Self,
    ) -> Result<&'b Self::Pointer<'bump>, AlreadyInitialized> {
        if !Self::is_ptr_valid(ptr) {
            // let nn_ptr = Self::ptr_to_raw(ptr).as_mut();
            // TODO change

            let mut b = Box::from_raw(Self::ptr_to_raw(ptr).as_mut() as *mut _);
            // core::ptr::drop_in_place(nn_ptr);
            // core::ptr::write(nn_ptr, Some(content));
            *b = Some(content);
            let nptr = NonNull::from(Box::leak(b));
            assert_eq!(nptr, Self::ptr_to_raw(ptr));
            Ok(ptr)
        } else {
            Err(AlreadyInitialized::Error)
        }
    }

    fn is_ptr_valid(ptr: &Self::Pointer<'bump>) -> bool {
        Self::ptr_to_ref(ptr).is_some()
    }
}

impl<'bump, T> Contained<'bump> for T
where
    T: Containable<'bump> + Sized + 'bump + std::fmt::Debug,
{
    type Pointer<'a>
        = Reference<'a, Self>
    where
        'bump: 'a;

    fn ptr_to_ref<'a>(ptr: &Self::Pointer<'bump>) -> &'a Option<Self>
    where
        'bump: 'a,
    {
        ptr.as_option_ref()
    }

    fn ptr_to_raw(ptr: &Self::Pointer<'bump>) -> NonNull<Option<Self>> {
        ptr.to_raw()
    }

    fn ptr_from_raw<'a>(
        ptr: NonNull<Option<Self>>,
        lt: PhantomData<&'bump Option<Self>>,
    ) -> Self::Pointer<'a>
    where
        'bump: 'a,
    {
        Reference::from_raw(ptr, lt)
    }
}
