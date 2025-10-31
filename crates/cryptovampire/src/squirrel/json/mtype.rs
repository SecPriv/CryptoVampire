use serde::{Deserialize, Serialize};

use super::Content;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub enum SortKind {
    Large,
    NameFixedLength,
    Finite,
    Fixed,
    WellFounded,
    Enum,
}

impl SortKind {
    // pub fn can_be_index(&self) -> bool {
    //     match self {
    //         SortKind::Finite | SortKind::Fixed | SortKind::Enum => true,
    //         _ => false,
    //     }
    // }

    /// Returns `true` if the sort kind is [`Enum`].
    ///
    /// [`Enum`]: SortKind::Enum
    #[must_use]
    pub fn is_enum(&self) -> bool {
        matches!(self, Self::Enum)
    }

    /// Returns `true` if the sort kind is [`WellFounded`].
    ///
    /// [`WellFounded`]: SortKind::WellFounded
    #[must_use]
    pub fn is_well_founded(&self) -> bool {
        matches!(self, Self::WellFounded)
    }

    /// Returns `true` if the sort kind is [`Fixed`].
    ///
    /// [`Fixed`]: SortKind::Fixed
    #[must_use]
    pub fn is_fixed(&self) -> bool {
        matches!(self, Self::Fixed)
    }

    /// Returns `true` if the sort kind is [`Finite`].
    ///
    /// [`Finite`]: SortKind::Finite
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite)
    }

    /// Returns `true` if the sort kind is [`NameFixedLength`].
    ///
    /// [`NameFixedLength`]: SortKind::NameFixedLength
    #[must_use]
    pub fn is_name_fixed_length(&self) -> bool {
        matches!(self, Self::NameFixedLength)
    }

    /// Returns `true` if the sort kind is [`Large`].
    ///
    /// [`Large`]: SortKind::Large
    #[must_use]
    pub fn is_large(&self) -> bool {
        matches!(self, Self::Large)
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SortData(pub Vec<SortKind>);

macro_rules! mk_is_funs {
    ($f:ident) => {
        #[allow(dead_code)]
        pub fn $f(&self) -> bool {
            self.0.iter().any(SortKind::$f)
        }
    };

    ($f0:ident, $($f:ident),*) => {
        mk_is_funs!($f0);
        mk_is_funs!($($f),*);
    }
}

impl SortData {
    pub fn can_be_index(&self) -> bool {
        (self.0.contains(&SortKind::Finite) && self.0.contains(&SortKind::Fixed))
            || self.0.contains(&SortKind::Enum)
    }

    mk_is_funs!(
        is_enum,
        is_well_founded,
        is_finite,
        is_fixed,
        is_name_fixed_length,
        is_large
    );
}
new_name!(SortName:Sort);
pub type Sort<'a> = Content<SortName<'a>, SortData>;
