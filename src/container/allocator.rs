use std::{convert::Infallible, error::Error};

use itertools::Itertools;

use crate::utils::utils::AlreadyInitialized;

use super::reference::Reference;

pub trait Container<'bump, R>
where
    R:  Reference<'bump>,
{
    fn allocate_pointee(
        &'bump self,
        content: Option<<R as Reference<'bump>>::Inner<'bump>>,
    ) -> &'bump Option<<R as Reference<'bump>>::Inner<'bump>>;
    fn allocate_uninit(&'bump self) -> &'bump Option<<R as Reference<'bump>>::Inner<'bump>> {
        self.allocate_pointee(Default::default())
    }
    fn allocate_inner(
        &'bump self,
        inner: <R as Reference<'bump>>::Inner<'bump>,
    ) -> &'bump Option<<R as Reference<'bump>>::Inner<'bump>> {
        self.allocate_pointee(Some(inner))
    }
}

pub trait ContainerTools<'bump, R> {
    type Inner<'a>
    where
        'a: 'bump;

    fn alloc_uninit(&'bump self) -> R;
    fn alloc_inner(&'bump self, inner: Self::Inner<'bump>) -> R;
    unsafe fn initialize(
        reference: &R,
        inner: Self::Inner<'bump>,
    ) -> Result<(), AlreadyInitialized>;

    fn alloc_cyclic<F>(&'bump self, f: F) -> Result<R, AlreadyInitialized>
    where
        F: for<'a> FnOnce(&'a R) -> Self::Inner<'bump>,
    {
        self.try_alloc_cyclic_with_residual(|u| Ok::<_, Infallible>((f(u), ())))
            .map(|(r, _)| r)
    }

    fn alloc_cyclic_with_residual<F, T>(&'bump self, f: F) -> Result<(R, T), AlreadyInitialized>
    where
        F: for<'a> FnOnce(&'a R) -> (Self::Inner<'bump>, T),
    {
        self.try_alloc_cyclic_with_residual(|u| {
            let (res, inner) = f(u);
            Ok::<_, Infallible>((res, inner))
        })
    }

    fn try_alloc_cyclic_with_residual<F, T, E1, E2>(&'bump self, f: F) -> Result<(R, T), E2>
    where
        F: for<'a> FnOnce(&'a R) -> Result<(Self::Inner<'bump>, T), E1>,
        E1: Error,
        E2: Error + From<E1> + From<AlreadyInitialized>,
    {
        let uninit = self.alloc_uninit();
        let (inner, res) = f(&uninit)?;
        unsafe { Self::initialize(&uninit, inner) }?;
        Ok((uninit, res))
    }
}

impl<'bump, C, R> ContainerTools<'bump, R> for C
where
    C: Container<'bump, R>,
    R:  Reference<'bump>,
{
    type Inner<'a> = <R as Reference<'bump>>::Inner<'a> where 'a:'bump;

    fn alloc_uninit(&'bump self) -> R {
        R::new_uninit(self)
    }

    unsafe fn initialize(
        reference: &R,
        inner: Self::Inner<'bump>,
    ) -> Result<(), AlreadyInitialized> {
        R::initialize_with(reference, inner).map(|_| ())
    }

    fn alloc_inner(&'bump self, inner: Self::Inner<'bump>) -> R {
        R::new_from(self, inner)
    }
}

impl<'bump, C, A, B> ContainerTools<'bump, (A, B)> for C
where
    C: ContainerTools<'bump, A> + ContainerTools<'bump, B>,
{
    type Inner<'a> = (
        <C as ContainerTools<'bump, A>>::Inner<'a>,
        <C as ContainerTools<'bump, B>>::Inner<'a>,
    ) where 'a:'bump;

    fn alloc_uninit(&'bump self) -> (A, B) {
        (self.alloc_uninit(), self.alloc_uninit())
    }

    unsafe fn initialize(
        reference: &(A, B),
        inner: Self::Inner<'bump>,
    ) -> Result<(), AlreadyInitialized> {
        let (a, b) = reference;
        let (ia, ib) = inner;
        Self::initialize(a, ia).and_then(|_| Self::initialize(b, ib))
    }

    fn alloc_inner(&'bump self, inner: Self::Inner<'bump>) -> (A, B) {
        let (a, b) = inner;
        (self.alloc_inner(a), self.alloc_inner(b))
    }
}

impl<'bump, C, R, const N: usize> ContainerTools<'bump, [R; N]> for C
where
    C: ContainerTools<'bump, R>,
{
    type Inner<'a> = [<C as ContainerTools<'bump, R>>::Inner<'a>; N] where 'a:'bump;

    fn alloc_uninit(&'bump self) -> [R; N] {
        std::array::from_fn(|_| self.alloc_uninit())
    }

    unsafe fn initialize(
        reference: &[R; N],
        inner: Self::Inner<'bump>,
    ) -> Result<(), AlreadyInitialized> {
        inner
            .into_iter()
            .zip_eq(reference.iter())
            .try_for_each(|(inner, reference)| unsafe { C::initialize(reference, inner) })
    }

    fn alloc_inner(&'bump self, inner: Self::Inner<'bump>) -> [R; N] {
        inner.map(|inner| self.alloc_inner(inner))
    }
}
