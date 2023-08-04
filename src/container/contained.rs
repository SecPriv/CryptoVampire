use crate::utils::utils::{AccessToInvalidData, AlreadyInitialized};

use super::{allocator::Container, reference::Reference};

pub trait Containable<'bump> {}

pub trait Contained<'bump>: 'bump + Sized {
    type Pointer<'a>: Sized
    where
        'bump: 'a;

    fn ptr_from_ref<'a>(ptr: &'bump Option<Self>) -> Self::Pointer<'a>
    where
        'bump: 'a;
    fn ptr_to_ref<'a>(ptr: &Self::Pointer<'bump>) -> &'a Option<Self>
    where
        'bump: 'a;

    fn new_ptr_uninit<'a, C>(container: &'bump C) -> Self::Pointer<'a>
    where
        C: Container<'bump, Self>,
        'bump: 'a,
    {
        Self::ptr_from_ref(container.allocate_uninit())
    }

    fn new_ptr_from_inner<'a, C>(container: &'bump C, content: Self) -> Self::Pointer<'a>
    where
        C: Container<'bump, Self>,
        'bump: 'a,
    {
        Self::ptr_from_ref(container.allocate_inner(content))
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
        if Self::is_ptr_valid(ptr) {
            let nn_ptr = Self::ptr_to_ref(ptr) as *const _ as *mut Option<Self>;
            core::ptr::drop_in_place(nn_ptr);
            core::ptr::write(nn_ptr, Some(content));
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
    T: Containable<'bump> + Sized + 'bump,
{
    type Pointer<'a> = Reference<'a, Self> where 'bump: 'a;

    fn ptr_from_ref<'a>(ptr: &'bump Option<Self>) -> Self::Pointer<'a>
    //Self::Pointer<'a>
    where
        'bump: 'a,
    {
        ptr.into()
    }

    fn ptr_to_ref<'a>(ptr: &Self::Pointer<'bump>) -> &'a Option<Self>
    where
        'bump: 'a,
    {
        ptr.as_option_ref()
    }
}
