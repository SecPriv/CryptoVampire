use super::Function;
use super::signature::FixedRefSignature;

// =========================================================
// =================== FixedSignature ======================
// =========================================================
/// Some function that has a fixed signature. It means it signature is
/// neither polymorphic nor variadic
pub trait FixedSignature<'a, 'bump>
where
    'bump: 'a,
    Self: 'a,
{
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump>;
}

/// To easily filter around functions that are [FixedSignature]
pub trait MaybeFixedSignature<'a, 'bump>
where
    'bump: 'a,
    Self: 'a,
{
    fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>>;

    fn has_fixed_signature(&'a self) -> bool {
        self.maybe_fixed_signature().is_some()
    }
}

impl<'a, 'bump, I> MaybeFixedSignature<'a, 'bump> for I
where
    I: FixedSignature<'a, 'bump>,
    'bump: 'a,
{
    fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>> {
        Some(self.as_fixed_signature())
    }
}

impl<'a, 'bump, I> MaybeFixedSignature<'a, 'bump> for Option<&'a I>
where
    I: MaybeFixedSignature<'a, 'bump>,
    'bump: 'a,
{
    fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>> {
        self.and_then(|s| s.maybe_fixed_signature())
    }
}

// =========================================================
// ===================== Evaluatable =======================
// =========================================================
/// Function that have an "evaluated" version of themselves
///
/// These are exclusively [TermAlgebra](super::inner::term_algebra::TermAlgebra)
/// functions.
pub trait Evaluatable<'bump> {
    fn get_evaluated(&self) -> Function<'bump>;
}

pub trait MaybeEvaluatable<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>>;
}

impl<'bump, I> MaybeEvaluatable<'bump> for I
where
    I: Evaluatable<'bump>,
{
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        Some(self.get_evaluated())
    }
}

impl<'bump, 'a, I> MaybeEvaluatable<'bump> for Option<&'a I>
where
    I: MaybeEvaluatable<'bump>,
{
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        self.and_then(MaybeEvaluatable::maybe_get_evaluated)
    }
}

// use paste::paste;

/// You don't want to know...
///
/// This horrendous things lets me (along with [macro_attr::macro_attr]) make my
/// own custom derive macros for all the trait that are here. I had to do this
/// because [`enum_dispach`](https://crates.io/crates/enum_dispatch) refuses to work
/// accross modules / with lifetimes
#[macro_export]
macro_rules! CustomDerive {
    (($($kind:tt),+) $(pub)? enum $name:ident { $($(#[$($attrs:tt)*])*$variant:ident$($vt:ty)?),* $(,)?}) => {
        CustomDerive!(
            @inner($($kind),*) $name
                {lifetimes}
                {type_vars }
                {variants $($variant($($vt)?)),*}
                {where lifetimes {} traits {}}
        );
    };

    (($($kind:tt),+) $(pub)? enum $name:ident<$($lt:lifetime),* $(,$tv:ident)*>
        {$($(#[$($attrs:tt)*])* $variant:ident$(($vt:ty))?),* $(,)?}) => {
        CustomDerive!(
            @inner($($kind),*) $name
            {lifetimes $($lt),*}
            {type_vars $($tv),*}
            {variants $($variant($($vt)?)),*}
            {where lifetimes {} traits {}}
        );
    };

    (($($kind:tt),+) $(pub)? enum $name:ident<$($lt:lifetime),* $(,$tv:ident)*>
        where
            $($lt_where1:lifetime : $lt_were:lifetime),*
            $($t_where1:ty : $t_where2:ty),*
        {$($(#[$($attrs:tt)*])* $variant:ident$($vt:ty)?),* $(,)?}) => {
        CustomDerive!(
            @inner($($kind),+) $name
            {lifetimes $($lt),*}
            {type_vars $($tv),*}
            {variants $($variant($($vt)?)),*}
            {where lifetimes {$($lt_where1:$lt_where2),*} traits {$($t_where1:$t_where2),*}}
        );
    };

    (@inner($kind:tt, no_bump, $bump:lifetime) $name:ident
            {lifetimes $($lt:lifetime),* $(,)?}
            {type_vars $($tv:ident),* $(,)?}
            {variants $($variant:ident$($vt:ty)?),* $(,)?}
            {where
                lifetimes {$($lt_where1:lifetime : $lt_were:lifetime),*}
                traits {$($t_where1:ty : $t_where2:ty),*}
            }
        ) => {CustomDerive!(
            @inner($kind, $bump) $name
            {lifetimes $($lt),*}
            {type_vars $($tv),*}
            {variants $($variant($($vt)?)),*}
            {where lifetimes {$($lt_where1:$lt_where2),*} traits {$($t_where1:$t_where2),*}}
            {extra bump $bump}
        );};

    (@inner(evaluate, $bump:lifetime) $name:ident
            {lifetimes $($lt:lifetime),* $(,)?}
            {type_vars $($tv:ident),* $(,)?}
            {variants $($variant:ident$($vt:ty)?),* $(,)?}
            {where
                lifetimes {$($lt_where1:lifetime : $lt_were:lifetime),*}
                traits {$($t_where1:ty : $t_where2:ty),*}
            }
            $({extra bump $bump2:lifetime})?
        ) => {
        impl<$($bump2,)? $($lt),* $($tv),* >
            $crate::formula::function::traits::Evaluatable<$bump>
            for $name< $($lt),* $($tv),*>
            where
                $($lt:$bump),*
                $($lt_where1:$lt_where2),*
                $($t_where1:$t_where2),*
        {
            fn get_evaluated(&self) -> $crate::formula::function::Function<'bump> {

                match self {
                        $(
                            Self::$variant(x) => x.get_evaluated()
                        ),*
                }
            }
        }
    };

    (@inner(maybe_evaluate, $bump:lifetime) $name:ident
            {lifetimes $($lt:lifetime),* $(,)?}
            {type_vars $($tv:ident),* $(,)?}
            {variants $($variant:ident$($vt:ty)?),* $(,)?}
            {where
                lifetimes {$($lt_where1:lifetime : $lt_were:lifetime),*}
                traits {$($t_where1:ty : $t_where2:ty),*}
            }
            $({extra bump $bump2:lifetime})?
        ) => {
        impl<$($bump2, )? $($lt),* $($tv),* >
            $crate::formula::function::traits::MaybeEvaluatable<$bump>
            for $name<$($lt),* $($tv),*>
            where
                $($lt:$bump),*
                $($lt_where1:$lt_where2),*
                $($t_where1:$t_where2),*
        {
            fn maybe_get_evaluated(&self) -> Option<$crate::formula::function::Function<'bump>>{
                match self {
                        $(
                            Self::$variant(x) =>  x.maybe_get_evaluated()
                        ),*
                }
            }
        }
    };

    (@inner(fixed_signature, $bump:lifetime) $name:ident
            {lifetimes $($lt:lifetime),* $(,)?}
            {type_vars $($tv:ident),* $(,)?}
            {variants $($variant:ident$($vt:ty)?),* $(,)?}
            {where
                lifetimes {$($lt_where1:lifetime : $lt_were:lifetime),*}
                traits {$($t_where1:ty : $t_where2:ty),*}
            }
            $({extra bump $bump2:lifetime})?
        ) => {
        impl<'ref_a, $($bump2, )? $($lt),* $($tv),* >
            $crate::formula::function::traits::FixedSignature<'ref_a, $bump>
            for $name<$($lt),* $($tv),*>
            where
                $($lt:$bump, $lt:'ref_a),*
                $($lt_where1:$lt_where2),*
                $($t_where1:$t_where2),*
                $($bump2: 'ref_a)?
        {
            fn as_fixed_signature(&'ref_a self) ->
                $crate::formula::function::signature::FixedRefSignature<'ref_a, 'bump>{
                match self {
                        $(
                            Self::$variant(x) =>  x.as_fixed_signature()
                        ),*
                }
            }
        }
    };

    (@inner(maybe_fixed_signature, $bump:lifetime) $name:ident
            {lifetimes $($lt:lifetime),* $(,)?}
            {type_vars $($tv:ident),* $(,)?}
            {variants $($variant:ident$($vt:ty)?),* $(,)?}
            {where
                lifetimes {$($lt_where1:lifetime : $lt_were:lifetime),*}
                traits {$($t_where1:ty : $t_where2:ty),*}
            }
            $({extra bump $bump2:lifetime})?
        ) => {
        impl<'ref_a, $($bump2, )? $($lt),* $($tv),* >
            $crate::formula::function::traits::MaybeFixedSignature<'ref_a, $bump>
            for $name<$($lt),* $($tv),*>
            where
                $($lt:$bump, $lt:'ref_a),*
                $($lt_where1:$lt_where2),*
                $($t_where1:$t_where2),*
                $($bump2: 'ref_a)?
        {
            fn maybe_fixed_signature(&'ref_a self) ->
                Option<$crate::formula::function::signature::FixedRefSignature<'ref_a, 'bump>>{
                match self {
                        $(
                            Self::$variant(x) =>  x.maybe_fixed_signature()
                        ),*
                }
            }
        }
    };
}
