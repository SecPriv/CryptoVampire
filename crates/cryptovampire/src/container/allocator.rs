use std::convert::Infallible;
use std::error::Error;
use std::fmt::Debug;
use std::ptr::NonNull;

use itertools::Itertools;
use log::error;
use utils::utils::AlreadyInitialized;

use super::contained::{Containable, Contained};

#[derive(Debug, Default)]
pub struct Residual<I, T> {
    // inner or reference
    pub content: I,
    pub residual: T,
}

impl<I, T> Residual<I, T> {
    pub fn content(&self) -> &I {
        &self.content
    }

    pub fn residual(&self) -> &T {
        &self.residual
    }
}

impl<I, T: Default> From<I> for Residual<I, T> {
    fn from(content: I) -> Self {
        Residual {
            content,
            residual: Default::default(),
        }
    }
}

pub trait Container<'bump, I>
where
    I: Contained<'bump>,
{
    fn allocate_pointee(&'bump self, content: Option<I>) -> NonNull<Option<I>>;
    fn allocate_uninit(&'bump self) -> NonNull<Option<I>> {
        self.allocate_pointee(Default::default())
    }
    fn allocate_inner(&'bump self, inner: I) -> NonNull<Option<I>> {
        self.allocate_pointee(Some(inner))
    }
}

#[allow(clippy::missing_safety_doc)] // FIXME
pub trait ContainerTools<'bump, I> {
    type R<'a>
    where
        'bump: 'a;

    fn alloc_uninit<'a>(&'bump self) -> Self::R<'a>
    where
        'bump: 'a;

    fn alloc_mulitple_uninit<'a, B>(&'bump self, n: usize) -> B
    where
        'bump: 'a,
        B: FromIterator<Self::R<'a>>,
    {
        std::iter::from_fn(|| Some(self.alloc_uninit()))
            .take(n)
            .collect()
    }

    /// # Safety: This part is implementation specific and likely to make a heavy use of usafe
    fn alloc_inner<'a>(&'bump self, inner: I) -> Self::R<'a>
    where
        'bump: 'a;
    unsafe fn initialize(reference: &Self::R<'bump>, inner: I) -> Result<(), AlreadyInitialized>;

    fn alloc_cyclic<F>(&'bump self, f: F) -> Result<Self::R<'bump>, AlreadyInitialized>
    where
        F: for<'b> FnOnce(&'b Self::R<'bump>) -> I,
        // 'bump: 'a,
    {
        self.try_alloc_cyclic_with_residual(|u| Ok::<_, Infallible>(f(u).into()))
            .map(
                |Residual {
                     content,
                     residual: (),
                 }| content,
            )
    }

    fn alloc_cyclic_with_residual<F, T>(
        &'bump self,
        f: F,
    ) -> Result<Residual<Self::R<'bump>, T>, AlreadyInitialized>
    where
        F: for<'b> FnOnce(&'b Self::R<'bump>) -> Residual<I, T>,
        // 'bump: 'a,
    {
        self.try_alloc_cyclic_with_residual(|u| {
            // let (inner, res) = f(u);
            Ok::<_, Infallible>(f(u))
        })
    }

    fn try_alloc_cyclic_with_residual<F, T, E1, E2>(
        &'bump self,
        f: F,
    ) -> Result<Residual<Self::R<'bump>, T>, E2>
    where
        F: for<'b> FnOnce(&'b Self::R<'bump>) -> Result<Residual<I, T>, E1>,
        E1: Error,
        E2: Error + From<E1> + From<AlreadyInitialized>,
    {
        let uninit = self.alloc_uninit();
        let Residual { content, residual } = f(&uninit)?;
        unsafe { Self::initialize(&uninit, content) }?;
        Ok(Residual {
            content: uninit,
            residual,
        })
    }

    fn try_alloc_mulitple_cyclic_with_residual<F, T, E1, E2, Iter1>(
        &'bump self,
        n: usize,
        f: F,
    ) -> Result<Residual<Vec<Self::R<'bump>>, T>, E2>
    where
        F: for<'b> FnOnce(&'b [Self::R<'bump>]) -> Result<Residual<Iter1, T>, E1>,
        E1: Error,
        E2: Error + From<E1> + From<AlreadyInitialized>,
        Iter1: IntoIterator<Item = I>,
    {
        // let uninit = self.alloc_uninit();
        let uninit: Vec<_> = self.alloc_mulitple_uninit(n);
        let Residual { content, residual } = f(&uninit)?;
        uninit
            .iter()
            .zip_eq(content)
            .try_for_each(|(reference, inner)| unsafe { Self::initialize(reference, inner) })?;

        // unsafe { Self::initialize(&uninit, content) }?;
        Ok(Residual {
            content: uninit,
            residual,
        })
    }
}

impl<'bump, C, I> ContainerTools<'bump, I> for C
where
    C: Container<'bump, I>,
    I: Contained<'bump> + Containable<'bump> + Debug,
{
    type R<'a>
        = I::Pointer<'a>
    where
        'bump: 'a;

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
        // if cfg!(debug_assertions) {
        if let Some(p) = I::ptr_to_ref(reference) {
            error!("{p:?}")
        }
        // }
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
    type R<'a>
        = (
        <C as ContainerTools<'bump, A>>::R<'a>,
        <C as ContainerTools<'bump, B>>::R<'a>,
    )
    where
        'bump: 'a;

    fn alloc_uninit<'a>(&'bump self) -> Self::R<'a>
    where
        'bump: 'a,
    {
        (
            <C as ContainerTools<'bump, A>>::alloc_uninit(self),
            <C as ContainerTools<'bump, B>>::alloc_uninit(self),
        )
    }

    fn alloc_inner<'a>(&'bump self, inner: (A, B)) -> Self::R<'a>
    where
        'bump: 'a,
    {
        let (a, b) = inner;
        (
            <C as ContainerTools<'bump, A>>::alloc_inner(self, a),
            <C as ContainerTools<'bump, B>>::alloc_inner(self, b),
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
        C::initialize(rb, b)?;
        Ok(())
    }
}

impl<'bump, C, I, const N: usize> ContainerTools<'bump, [I; N]> for C
where
    C: ContainerTools<'bump, I>,
{
    type R<'a>
        = [<C as ContainerTools<'bump, I>>::R<'a>; N]
    where
        'bump: 'a;

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
    ) -> Result<(), AlreadyInitialized> {
        inner
            .into_iter()
            .zip_eq(reference.iter())
            .try_for_each(|(inner, reference)| unsafe { C::initialize(reference, inner) })
    }
}
