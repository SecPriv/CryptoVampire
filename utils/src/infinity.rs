use std::fmt::Display;

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum Infinity<Idx> {
    LowInfinity,
    Num(Idx),
    HighInfinty,
}

impl<Idx: Display> Display for Infinity<Idx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LowInfinity => write!(f, "-∞"),
            Self::HighInfinty => write!(f, "+∞"),
            Self::Num(x) => write!(f, "{x}"),
        }
    }
}

impl<Idx> From<Idx> for Infinity<Idx> {
    #[inline]
    fn from(value: Idx) -> Self {
        Self::Num(value)
    }
}

// impl<Idx: PartialOrd> PartialOrd for Infinity<Idx> {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         match (self, other) {
//             (Infinity::LowInfinity, Infinity::LowInfinity)
//             | (Infinity::HighInfinty, Infinity::HighInfinty) => Some(Ordering::Equal),
//             (Infinity::LowInfinity, _) | (_, Infinity::HighInfinty) => Some(Ordering::Less),
//             (_, Infinity::LowInfinity) | (Infinity::HighInfinty, _) => Some(Ordering::Greater),
//             (Infinity::Num(a), Infinity::Num(b)) => Idx::partial_cmp(a, b),
//         }
//     }
// }

// impl<Idx:Ord> Ord for Infinity<Idx>

#[cfg(test)]
mod tests {
    use crate::infinity::Infinity;

    #[test]
    fn lower_infinity_is_smaller() {
        assert!(Infinity::LowInfinity::<usize> < Infinity::HighInfinty);
        assert!(Infinity::LowInfinity < Infinity::Num(34));
    }
    #[test]
    fn high_infinity_is_bigger() {
        assert!(Infinity::LowInfinity::<usize> < Infinity::HighInfinty);
        assert!(Infinity::HighInfinty > Infinity::Num(34));
        assert!(Infinity::LowInfinity < Infinity::Num(34));
    }

    #[test]
    fn number_have_the_right_order() {
        assert!(Infinity::Num(34534) < Infinity::Num(438276582))
    }
}
