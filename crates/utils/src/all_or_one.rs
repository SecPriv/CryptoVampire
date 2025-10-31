use std::error::Error;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use if_chain::if_chain;
use itertools::{Either, Itertools};

use crate::monad::{Monad, MonadFamily, MonadFamilyMember};
use crate::{implvec, mdo};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AllOrOne<U, V> {
    All(V),
    Any(U),
    One(usize, U),
}

pub type AllOrOneShape = AllOrOne<(), usize>;

pub type AoOV<U> = AllOrOne<U, Vec<U>>;

impl AllOrOneShape {
    pub fn try_merge(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::One(_, ()), _) | (_, Self::One(_, ())) => {
                if_chain! {
                    if let Self::One(i, _) = self;
                    if let Self::One(j, _) = other;
                    if i == j;
                    then {
                        Some(Self::One(i, ()))
                    } else {
                        None
                    }
                }
            }
            (Self::All(i), Self::All(j)) => {
                if i == j {
                    Some(Self::All(i))
                } else {
                    None
                }
            }
            (Self::All(i), _) | (_, Self::All(i)) => Some(Self::All(i)),
            (Self::Any(()), Self::Any(())) => Some(Self::Any(())),
        }
    }

    pub fn merge(self, other: Self) -> Self {
        self.try_merge(other).unwrap()
    }

    pub fn monad_continue<U2>(self, mut f: impl FnMut() -> AoOV<U2>) -> AoOV<U2> {
        match self {
            AllOrOne::All(l) => AllOrOne::All((0..l).map(|i| f().owned_get(i)).collect()),
            AllOrOne::Any(_) => {
                let r = f();
                assert!(matches!(r, AllOrOne::All(_) | AllOrOne::Any(_)));
                r
            }
            AllOrOne::One(i, _) => AllOrOne::One(i, f().owned_get(i)),
        }
    }

    pub fn to_aoov(self) -> AoOV<()> {
        match self {
            AllOrOne::All(size) => AllOrOne::All(vec![(); size]),
            AllOrOne::Any(()) => AllOrOne::Any(()),
            AllOrOne::One(i, ()) => AllOrOne::One(i, ()),
        }
    }
}

impl<U, V> AllOrOne<U, V>
where
    V: AsRef<[U]>,
{
    pub fn shape(&self) -> AllOrOneShape {
        match self {
            AllOrOne::All(l) => AllOrOne::All(l.as_ref().len()),
            AllOrOne::Any(_) => AllOrOne::Any(()),
            AllOrOne::One(i, _) => AllOrOne::One(*i, ()),
        }
    }

    pub fn as_ref(&self) -> AllOrOne<&U, &[U]> {
        match self {
            AllOrOne::All(l) => AllOrOne::All(l.as_ref()),
            AllOrOne::Any(u) => AllOrOne::Any(u),
            AllOrOne::One(i, u) => AllOrOne::One(*i, u),
        }
    }
}

impl<U, V> AllOrOne<U, V>
where
    V: Deref<Target = [U]>,
{
    pub fn get(&self, i: usize) -> Option<&U> {
        match self {
            AllOrOne::All(l) => l.get(i),
            AllOrOne::Any(x) => Some(x),
            AllOrOne::One(j, x) if i == *j => Some(x),
            _ => None,
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> Option<usize> {
        match self {
            Self::All(l) => Some(l.len()),
            _ => None,
        }
    }
}

impl<U, V> AllOrOne<U, V>
where
    V: DerefMut<Target = [U]>,
{
    pub fn get_mut(&mut self, i: usize) -> Option<&mut U> {
        match self {
            AllOrOne::All(l) => l.get_mut(i),
            AllOrOne::Any(x) => Some(x),
            AllOrOne::One(j, x) if i == *j => Some(x),
            _ => None,
        }
    }
}

impl<U, V> AllOrOne<U, V>
where
    V: IntoIterator<Item = U>,
{
    pub fn map<F, U2, V2>(self, mut f: F) -> AllOrOne<U2, V2>
    where
        V2: FromIterator<U2>,
        F: FnMut(U) -> U2,
    {
        match self {
            AllOrOne::All(l) => AllOrOne::All(l.into_iter().map(f).collect()),
            AllOrOne::Any(x) => AllOrOne::Any(f(x)),
            AllOrOne::One(i, x) => AllOrOne::One(i, f(x)),
        }
    }
}

impl<U: Default, V> Default for AllOrOne<U, V> {
    fn default() -> Self {
        AllOrOne::Any(Default::default())
    }
}
impl<U> AoOV<U> {
    pub fn owned_get(self, i: usize) -> U {
        match self {
            AllOrOne::All(mut l) => l.swap_remove(i),
            AllOrOne::Any(x) => x,
            AllOrOne::One(j, x) if i == j => x,
            _ => panic!("out of bounds"),
        }
    }

    /// likely to panic if f return a `One` or an array that is not long enough
    pub fn monad_continue<U2>(self, mut f: impl FnMut(U) -> AoOV<U2>) -> AoOV<U2> {
        match self {
            AllOrOne::All(l) => AllOrOne::All(
                l.into_iter()
                    .enumerate()
                    .map(|(i, e)| f(e).owned_get(i))
                    .collect(),
            ),
            AllOrOne::Any(e) => {
                let r = f(e);
                assert!(matches!(r, AllOrOne::All(_) | AllOrOne::Any(_)));
                r
            }
            AllOrOne::One(i, e) => AllOrOne::One(i, f(e).owned_get(i)),
        }
    }

    pub fn any(u: U) -> Self {
        Self::Any(u)
    }
}

impl<U: Clone> AoOV<U> {
    pub fn transpose_array<const N: usize>(args: [Self; N]) -> AoOV<[U; N]> {
        let args = Vec::from(args);
        mdo! {
            let! l = AoOV::transpose_iter(args);
            pure l.try_into().map_err(|_| ()).unwrap()
        }
    }

    /// keep the length of the array
    pub fn transpose_iter(args: implvec!(Self)) -> AoOV<Vec<U>> {
        let args: Vec<_> = args.into_iter().collect();
        let goal = args
            .iter()
            .map(|x| x.shape())
            .fold(AllOrOne::default(), AllOrOne::merge);

        match goal {
            AllOrOne::All(size) => AllOrOne::All(
                (0..size)
                    .map(|i| args.iter().map(|x| x.get(i).unwrap().clone()).collect())
                    .collect(),
            ),
            AllOrOne::Any(_) => AllOrOne::Any(args.into_iter().map(|x| x.owned_get(0)).collect()),
            AllOrOne::One(i, _) => {
                AllOrOne::One(i, args.into_iter().map(|x| x.owned_get(i)).collect())
            }
        }
    }
}

impl<U> AoOV<Option<U>> {
    pub fn transpose(self) -> Option<AoOV<U>> {
        match self {
            AllOrOne::All(arg) => {
                let arg: Option<Vec<_>> = arg.into_iter().collect();
                arg.map(|arg| AllOrOne::All(arg))
            }
            AllOrOne::Any(Some(arg)) => Some(AllOrOne::Any(arg)),
            AllOrOne::One(i, Some(arg)) => Some(AllOrOne::One(i, arg)),
            _ => None,
        }
    }
}

impl<U, E> AoOV<Result<U, E>> {
    pub fn transpose(self) -> Result<AoOV<U>, E> {
        match self {
            AllOrOne::All(arg) => {
                let arg: Result<Vec<_>, E> = arg.into_iter().collect();
                arg.map(|arg| AllOrOne::All(arg))
            }
            AllOrOne::Any(Ok(arg)) => Ok(AllOrOne::Any(arg)),
            AllOrOne::One(i, Ok(arg)) => Ok(AllOrOne::One(i, arg)),
            AllOrOne::Any(Err(e)) | AllOrOne::One(_, Err(e)) => Err(e),
        }
    }
}

impl<U> IntoIterator for AoOV<U> {
    type Item = U;

    type IntoIter = Either<std::vec::IntoIter<U>, std::array::IntoIter<U, 1>>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            AllOrOne::All(v) => Either::Left(v.into_iter()),
            AllOrOne::Any(x) | AllOrOne::One(_, x) => Either::Right([x].into_iter()),
        }
    }
}

pub struct AllOrOneMonadicFamilly;

impl MonadFamily for AllOrOneMonadicFamilly {
    type Member<T> = AoOV<T>;
}

impl<T> MonadFamilyMember<T> for AoOV<T> {
    type Of = AllOrOneMonadicFamilly;
}

impl<T> Monad<T> for AoOV<T> {
    fn pure(u: T) -> Self {
        AllOrOne::Any(u)
    }

    fn bind<B>(self, f: impl FnMut(T) -> AoOV<B>) -> AoOV<B> {
        self.monad_continue(f)
    }
}

pub struct AllOrOneResultMonadicFamilly<E: Error>(PhantomData<E>);

impl<E: Error> MonadFamily for AllOrOneResultMonadicFamilly<E> {
    type Member<T> = Result<AoOV<T>, E>;
}

impl<T, E: Error> MonadFamilyMember<T> for Result<AoOV<T>, E> {
    type Of = AllOrOneResultMonadicFamilly<E>;
}

impl<T, E: Error> Monad<T> for Result<AoOV<T>, E> {
    fn pure(u: T) -> Self {
        Ok(AllOrOne::pure(u))
    }

    fn bind<B>(self, mut f: impl FnMut(T) -> Result<AoOV<B>, E>) -> Result<AoOV<B>, E> {
        let s = self?;
        Ok(match s {
            AllOrOne::All(l) => {
                let l = l
                    .into_iter()
                    .map(f)
                    .enumerate()
                    .map(|(i, e)| e.map(|x| x.owned_get(i)))
                    .try_collect()?;
                AllOrOne::All(l)
            }
            AllOrOne::Any(e) => {
                let r = f(e)?;
                assert!(matches!(r, AllOrOne::All(_) | AllOrOne::Any(_)));
                r
            }
            AllOrOne::One(i, e) => AllOrOne::One(i, f(e)?.owned_get(i)),
        })
    }
}
