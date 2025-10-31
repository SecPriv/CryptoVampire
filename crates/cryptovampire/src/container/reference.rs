use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ptr::NonNull;

use log::error;
use utils::precise_as_ref::PreciseAsRef;
use utils::string_ref::StrRef;
use utils::traits::RefNamed;
use utils::utils::MaybeInvalid;

// pub type RefPointee<'bump, R> = Option<<R as Reference<'bump>>::Inner>;
// pub type RefInner<'bump, R> = <R as Reference<'bump>>::Inner;

pub struct Reference<'bump, T> {
    inner: NonNull<Option<T>>,
    lt: PhantomData<&'bump ()>,
}

unsafe impl<'bump, T: Sync> Sync for Reference<'bump, T> {}
unsafe impl<'bump, T: Sync> Send for Reference<'bump, T> {}

/// [Reference] but with a forced order based on the value of the pointer.
///
/// This is non-deterministic
// #[deprecated]
pub struct FORef<'bump, T>(Reference<'bump, T>);

impl<'bump, T> Reference<'bump, T> {
    pub fn as_option_ref(&self) -> &'bump Option<T> {
        if super::PRINT_DEREF {
            error!(
                "deref NonNul at {} in {}\n\t(for {})",
                line!(),
                file!(),
                std::any::type_name::<Self>()
            );
        }
        unsafe { self.to_raw().as_ref() }
    }

    pub fn as_inner(&self) -> &T {
        self.as_ref()
    }

    pub fn maybe_precise_as_ref(&self) -> Option<&'bump T> {
        self.as_option_ref().as_ref()
    }

    pub fn from_raw(ptr: NonNull<Option<T>>, _lt: PhantomData<&'bump Option<T>>) -> Self {
        Self {
            inner: ptr,
            lt: Default::default(),
        }
    }

    pub fn to_raw(&self) -> NonNull<Option<T>> {
        self.inner
    }

    pub fn as_fo(&self) -> FORef<'bump, T> {
        (*self).into()
    }
}

impl<'bump, T> PreciseAsRef<'bump, T> for Reference<'bump, T> {
    fn precise_as_ref(&self) -> &'bump T {
        self.maybe_precise_as_ref().unwrap()
    }
}

impl<'bump, T> AsRef<T> for Reference<'bump, T> {
    fn as_ref(&self) -> &T {
        self.precise_as_ref()
    }
}

impl<'bump, T> PartialEq for Reference<'bump, T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<'bump, T> Eq for Reference<'bump, T> {}

impl<'bump, T: Ord> Ord for Reference<'bump, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            Ordering::Equal
        } else {
            match Ord::cmp(self.as_inner(), other.as_inner()) {
                Ordering::Equal => Ord::cmp(&self.inner, &other.inner),
                o => o,
            }
        }
    }
}

impl<'bump, T: PartialOrd> PartialOrd for Reference<'bump, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            match PartialOrd::partial_cmp(self.as_inner(), other.as_inner()) {
                Some(Ordering::Equal) => PartialOrd::partial_cmp(&self.inner, &other.inner),
                o => o,
            }
        }
    }
}

impl<'b, T: Debug> Debug for Reference<'b, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
        // write!(f, "Ref {{ptr: {:?}, inner: {:?} }}", self.inner, self.as_inner())
    }
}

impl<'bump, T> MaybeInvalid for Reference<'bump, T> {
    fn is_valid(&self) -> bool {
        self.maybe_precise_as_ref().is_some()
    }
}

// impl<'bump, T> From<&'bump Option<T>> for Reference<'bump, T> {
//     fn from(value: &'bump Option<T>) -> Self {
//         Self {
//             inner: NonNull::from(value),
//             lt: Default::default(),
//         }
//     }
// }

#[allow(clippy::non_canonical_clone_impl)]
impl<'bump, T> Clone for Reference<'bump, T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner,
            lt: Default::default(),
        }
    }
}

impl<'bump, T> Copy for Reference<'bump, T> {}

impl<'bump, T: Hash> Hash for Reference<'bump, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl<'a, 'bump: 'a, T> RefNamed<'a> for Reference<'bump, T>
where
    &'bump T: RefNamed<'bump> + 'bump,
{
    fn name_ref(&self) -> StrRef<'a> {
        self.precise_as_ref().name_ref()
    }
}

// -----------------------------------------------------------------------------
// ---------------------------------- FORef ------------------------------------
// -----------------------------------------------------------------------------

impl<'bump, T> FORef<'bump, T> {
    pub fn as_reference(&self) -> Reference<'bump, T> {
        self.0
    }

    pub fn as_usize(&self) -> usize {
        self.0.inner.as_ptr() as usize
    }
}

impl<'bump, T> PartialOrd for FORef<'bump, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<'bump, T> Ord for FORef<'bump, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.inner.cmp(&other.0.inner)
    }
}
impl<'bump, T> Hash for FORef<'bump, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.inner.hash(state);
    }
}
impl<'bump, T> Eq for FORef<'bump, T> {}
impl<'bump, T> PartialEq for FORef<'bump, T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.inner == other.0.inner
    }
}
impl<'bump, T> Copy for FORef<'bump, T> {}
impl<'bump, T> Clone for FORef<'bump, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'bump, T: Debug> Debug for FORef<'bump, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_reference().fmt(f)
    }
}

// -----------------------------------------------------------------------------
// -------------------------------- From & co ----------------------------------
// -----------------------------------------------------------------------------

impl<'bump, T> From<Reference<'bump, T>> for FORef<'bump, T> {
    fn from(value: Reference<'bump, T>) -> Self {
        FORef(value)
    }
}

impl<'bump, T> From<FORef<'bump, T>> for Reference<'bump, T> {
    fn from(value: FORef<'bump, T>) -> Self {
        value.0
    }
}

// impl<'bump, T> Borrow<Reference<'bump, T>> for FORef<'bump, T> {
//     fn borrow(&self) -> &Reference<'bump, T> {
//         &self.0
//     }
// }
