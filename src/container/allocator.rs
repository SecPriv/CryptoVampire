use std::{convert::Infallible, error::Error};

use itertools::Itertools;

use crate::utils::utils::AlreadyInitialized;

use super::{
    contained::{Containable, Contained},
    reference::Reference,
};

pub trait Container<'bump, I>
where
    I: Contained<'bump>,
{
    fn allocate_pointee(&'bump self, content: Option<I>) -> &'bump Option<I>;
    fn allocate_uninit(&'bump self) -> &'bump Option<I> {
        self.allocate_pointee(Default::default())
    }
    fn allocate_inner(&'bump self, inner: I) -> &'bump Option<I> {
        self.allocate_pointee(Some(inner))
    }
}

pub trait ContainerTools<'bump, I> {
    type R<'a>
    where
        'bump: 'a;

    fn alloc_uninit<'a>(&'bump self) -> Self::R<'a>
    where
        'bump: 'a;
    fn alloc_inner<'a>(&'bump self, inner: I) -> Self::R<'a>
    where
        'bump: 'a;
    unsafe fn initialize(reference: &Self::R<'bump>, inner: I) -> Result<(), AlreadyInitialized>;
    // where
    //     'bump: 'a;

    fn alloc_cyclic< F>(&'bump self, f: F) -> Result<Self::R<'bump>, AlreadyInitialized>
    where
        F: for<'b> FnOnce(&'b Self::R<'bump>) -> I,
        // 'bump: 'a,
    {
        self.try_alloc_cyclic_with_residual(|u| Ok::<_, Infallible>((f(u), ())))
            .map(|(r, _)| r)
    }

    fn alloc_cyclic_with_residual< F, T>(
        &'bump self,
        f: F,
    ) -> Result<(Self::R<'bump>, T), AlreadyInitialized>
    where
        F: for<'b> FnOnce(&'b Self::R<'bump>) -> (I, T),
        // 'bump: 'a,
    {
        self.try_alloc_cyclic_with_residual(|u| {
            let (res, inner) = f(u);
            Ok::<_, Infallible>((res, inner))
        })
    }

    fn try_alloc_cyclic_with_residual< F, T, E1, E2>(
        &'bump self,
        f: F,
    ) -> Result<(Self::R<'bump>, T), E2>
    where
        F: for<'b> FnOnce(&'b Self::R<'bump>) -> Result<(I, T), E1>,
        E1: Error,
        E2: Error + From<E1> + From<AlreadyInitialized>,
    {
        let uninit = self.alloc_uninit();
        let (inner, res) = f(&uninit)?;
        unsafe { Self::initialize(&uninit, inner) }?;
        Ok((uninit, res))
    }
}

impl<'bump, C, I> ContainerTools<'bump, I> for C
where
    C: Container<'bump, I>,
    I: Contained<'bump> + Containable<'bump>,
{
    type R<'a> = I::Pointer<'a> where 'bump:'a;

    fn alloc_uninit<'a>(&'bump self) -> Self::R<'a>
    where
        'bump: 'a,
    {
        I::new_ptr_uninit(self)
    }

    fn alloc_inner<'a>(&'bump self, inner: I) -> Self::R<'a>
    where
        'bump: 'a,
    {
        I::new_ptr_from_inner(self, inner)
    }

    unsafe fn initialize(reference: &Self::R<'bump>, inner: I) -> Result<(), AlreadyInitialized>
    // where
    //     'bump: 'a,
    {
        I::initialize_with(reference, inner).map(|_| ())
    }
    // type R<'a> = I::Pointer<'a> where 'bump:'a;

    // fn alloc_uninit<'a>(&'bump self) -> Self::R<'a> where 'bump:'a {
    //     R::new_uninit(self)
    // }

    // unsafe fn initialize(reference: &R, inner: Self::Inner) -> Result<(), AlreadyInitialized> {
    //     R::initialize_with(reference, inner).map(|_| ())
    // }

    // fn alloc_inner(&'bump self, inner: Self::Inner) -> R {
    //     R::new_from(self, inner)
    // }
}

impl<'bump, C, A, B> ContainerTools<'bump, (A, B)> for C
where
    C: ContainerTools<'bump, A> + ContainerTools<'bump, B>,
{
    type R<'a> = (<C as ContainerTools<'bump, A>>::R<'a>
        , <C as ContainerTools<'bump, B>>::R<'a>) where 'bump:'a;

    fn alloc_uninit<'a>(&'bump self) -> Self::R<'a>
    where
        'bump: 'a,
    {
        (
            <C as ContainerTools<'bump, A>>::alloc_uninit(&self),
            <C as ContainerTools<'bump, B>>::alloc_uninit(&self),
        )
    }

    fn alloc_inner<'a>(&'bump self, inner: (A, B)) -> Self::R<'a>
    where
        'bump: 'a,
    {
        let (a, b) = inner;
        (
            <C as ContainerTools<'bump, A>>::alloc_inner(&self, a),
            <C as ContainerTools<'bump, B>>::alloc_inner(&self, b),
        )
    }

    unsafe fn initialize(
        reference: &Self::R<'bump>,
        inner: (A, B),
    ) -> Result<(), AlreadyInitialized>
    // where
    //     'bump: 'a,
    {
        let (a, b) = inner;
        let (ra, rb) = reference;
        C::initialize(ra, a)?;
        C::initialize(rb, b);
        Ok(())
    }
}

impl<'bump, C, I, const N: usize> ContainerTools<'bump, [I; N]> for C
where
    C: ContainerTools<'bump, I>,
{
    type R<'a> = [<C as ContainerTools<'bump, I>>::R<'a>; N] where 'bump:'a;

    fn alloc_uninit<'a>(&'bump self) -> Self::R<'a>
    where
        'bump: 'a,
    {
        std::array::from_fn(|_| self.alloc_uninit())
    }

    fn alloc_inner<'a>(&'bump self, inner: [I; N]) -> Self::R<'a>
    where
        'bump: 'a,
    {
        inner.map(|inner| self.alloc_inner(inner))
    }

    unsafe fn initialize(
        reference: &Self::R<'bump>,
        inner: [I; N],
    ) -> Result<(), AlreadyInitialized>
    // where
    //     'bump: 'a,
    {
        inner
            .into_iter()
            .zip_eq(reference.iter())
            .try_for_each(|(inner, reference)| unsafe { C::initialize(reference, inner) })
    }

    // fn alloc_uninit<'a>(&'a self) -> [I; N] {
    //     std::array::from_fn(|_| self.alloc_uninit())
    // }

    // unsafe fn initialize(reference: &[I; N], inner: [I; N]) -> Result<(), AlreadyInitialized> {
    //     inner
    //         .into_iter()
    //         .zip_eq(reference.iter())
    //         .try_for_each(|(inner, reference)| unsafe { C::initialize(reference, inner) })
    // }

    // fn alloc_inner(&'bump self, inner: [I; N]) -> [I; N] {
    //     inner.map(|inner| self.alloc_inner(inner))
    // }
}
