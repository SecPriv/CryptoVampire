use super::*;
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum HeadSk<Var, Fun, Quant> {
    Var(Var),
    Fun(Fun),
    Quant(Quant),
}
pub type Head<F> = HeadSk<<F as Formula>::Var, <F as Formula>::Fun, <F as Formula>::Quant>;

impl<Var, Fun, Quant> HeadSk<Var, Fun, Quant> {
    #[must_use]
    pub fn as_var(&self) -> Option<&Var> {
        if let Self::Var(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_fun(&self) -> Option<&Fun> {
        if let Self::Fun(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_quant(&self) -> Option<&Quant> {
        if let Self::Quant(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn try_into_var(self) -> Result<Var, Self> {
        if let Self::Var(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    /// Returns `true` if the head sk is [`Var`].
    ///
    /// [`Var`]: HeadSk::Var
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(..))
    }

    /// Returns `true` if the head sk is [`Fun`].
    ///
    /// [`Fun`]: HeadSk::Fun
    #[must_use]
    pub fn is_fun(&self) -> bool {
        matches!(self, Self::Fun(..))
    }

    #[must_use]
    pub fn try_into_fun(self) -> Result<Fun, Self> {
        if let Self::Fun(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    /// Returns `true` if the head sk is [`Quant`].
    ///
    /// [`Quant`]: HeadSk::Quant
    #[must_use]
    pub fn is_quant(&self) -> bool {
        matches!(self, Self::Quant(..))
    }

    #[must_use]
    pub fn try_into_quant(self) -> Result<Quant, Self> {
        if let Self::Quant(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
}
