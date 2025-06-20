use egg::VarExposed;
use steel::rvals::{FromSteelVal, IntoSteelVal};
use steel_derive::Steel;

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

impl From<egg::Var> for SVar {
    fn from(value: egg::Var) -> Self {
        let VarExposed::Num(i) = value.expose() else {unimplemented!()};
        Self(i)
    }
}

impl Into<egg::Var> for SVar {
    fn into(self) -> egg::Var {
        egg::Var::from_u32(self.0)
    }
}