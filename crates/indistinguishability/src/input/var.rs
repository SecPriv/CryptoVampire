use steel::rvals::{FromSteelVal, IntoSteelVal};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SVar(u32);

impl FromSteelVal for SVar {
    fn from_steelval(val: &steel::SteelVal) -> steel::rvals::Result<Self> {
        Ok(Self(FromSteelVal::from_steelval(val)?))
    }
}

impl IntoSteelVal for SVar {
    fn into_steelval(self) -> steel::rvals::Result<steel::SteelVal> {
        self.0.into_steelval()
    }
}