use crate::implvec;

//thank you https://stackoverflow.com/a/78171691/10875409
pub trait MonadFamily {
    type Member<T>: Monad<T>;
}

pub trait MonadFamilyMember<T> {
    type Of: MonadFamily<Member<T> = Self>;
}
pub trait Monad<A>: MonadFamilyMember<A> {
    fn pure(u: A) -> Self;
    fn bind<B>(
        self,
        f: impl FnMut(A) -> <Self::Of as MonadFamily>::Member<B>,
    ) -> <Self::Of as MonadFamily>::Member<B>;
}

#[macro_export]
macro_rules! mdo {
  (pure $e:expr ) => {$crate::monad::Monad::pure($e)};
  (let($t:ty) $v:pat = $e:expr; $($rest:tt)*) => {
    <$t as $crate::monad::Monad<_>>::pure($e)
      .bind(|$v| { $crate::mdo!($($rest)*)} )
  };
  (let($t:ty) $v:pat = $t2:ty = $e:expr; $($rest:tt)*) => {
    <$t as $crate::monad::Monad<$t2>>::pure($e)
      .bind(|$v| { $crate::mdo!($($rest)*)} )
  };
  (let! $v:pat = $monad:expr ; $($rest:tt)* ) => {
    ($monad).bind( |$v| { $crate::mdo!($($rest)*)})
  };
  (let! $v:ident : $t:ty = $monad:expr ; $($rest:tt)* ) => {
    ($monad).bind( |$v : $t| { $crate::mdo!($($rest)*)})
  };
  (move let! $v:pat = $monad:expr ; $($rest:tt)* ) => {
    ($monad).bind( move |$v| { $crate::mdo!($($rest)*)})
  };
  (move let! $v:ident : $t:ty = $monad:expr ; $($rest:tt)* ) => {
    ($monad).bind( move |$v:$t| { $crate::mdo!($($rest)*)})
  };
  (block $monad:block) => {$monad};
  ($monad:expr;!) => {$monad};
}

#[cfg(test)]
mod test {
    use super::*;

    pub struct VecFamily;

    impl MonadFamily for VecFamily {
        type Member<T> = Vec<T>;
    }

    impl<T> MonadFamilyMember<T> for Vec<T> {
        type Of = VecFamily;
    }

    impl<A> Monad<A> for Vec<A> {
        fn pure(u: A) -> Self {
            vec![u]
        }

        fn bind<B>(
            self,
            f: impl FnMut(A) -> <Self::Of as MonadFamily>::Member<B>,
        ) -> <Self::Of as MonadFamily>::Member<B> {
            self.into_iter().flat_map(f).collect()
        }
    }

    #[test]
    fn test() {
        let array = mdo! {
          let(Vec<i32>) x = 3 ;
          let! a = vec![4, 5];
          let! [b] = vec![[6], [7]];
          pure (x * a * b)
        };
        assert_eq!(vec![3 * 4 * 6, 3 * 4 * 7, 3 * 5 * 6, 3 * 5 * 7], array)
    }
}
