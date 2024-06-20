use crate::problem::cell::MemoryCell;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum CellOrInput<'bump> {
    Input,
    Cell(MemoryCell<'bump>),
}

impl<'bump> CellOrInput<'bump> {
    #[must_use]
    pub fn into_option(self) -> Option<MemoryCell<'bump>> {
        self.into()
    }

    /// Returns `true` if the cell or input is [`Input`].
    ///
    /// [`Input`]: CellOrInput::Input
    #[must_use]
    pub fn is_input(&self) -> bool {
        matches!(self, Self::Input)
    }

    /// Returns `true` if the cell or input is [`Cell`].
    ///
    /// [`Cell`]: CellOrInput::Cell
    #[must_use]
    pub fn is_cell(&self) -> bool {
        matches!(self, Self::Cell(..))
    }

    #[must_use]
    pub fn as_cell(&self) -> Option<MemoryCell<'bump>> {
      self.into_option()
    }

    #[must_use]
    pub fn try_into_cell(self) -> Result<MemoryCell<'bump>, Self> {
        if let Self::Cell(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
}

impl<'bump, F> From<Option<F>> for CellOrInput<'bump>
where
    F: Into<MemoryCell<'bump>>,
{
    fn from(value: Option<F>) -> Self {
        match value {
            None => Self::Input,
            Some(x) => Self::Cell(x.into()),
        }
    }
}
impl<'bump, F> From<F> for CellOrInput<'bump>
where
    F: Into<MemoryCell<'bump>>,
{
    fn from(value: F) -> Self {
        Self::Cell(value.into())
    }
}

impl<'bump> Into<Option<MemoryCell<'bump>>> for CellOrInput<'bump> {
    fn into(self) -> Option<MemoryCell<'bump>> {
        match self {
            Self::Input => None,
            Self::Cell(x) => Some(x),
        }
    }
}
