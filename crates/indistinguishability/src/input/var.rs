use steel::rvals::{FromSteelVal, IntoSteelVal};

/// Represents a Steel variable, wrapping a `u32`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SVar(u32);

impl FromSteelVal for SVar {
    /// Converts a `SteelVal` into an `SVar`.
    fn from_steelval(val: &steel::SteelVal) -> steel::rvals::Result<Self> {
        Ok(Self(FromSteelVal::from_steelval(val)?))
    }
}

impl IntoSteelVal for SVar {
    /// Converts an `SVar` into a `SteelVal`.
    fn into_steelval(self) -> steel::rvals::Result<steel::SteelVal> {
        self.0.into_steelval()
    }
}
