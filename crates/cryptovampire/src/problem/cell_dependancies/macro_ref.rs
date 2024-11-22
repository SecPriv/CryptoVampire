use crate::problem::cell::MemoryCell;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum MacroRef<'bump> {
    Input,
    Exec,
    Cell(MemoryCell<'bump>),
}

impl<'bump> MacroRef<'bump> {
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

    pub fn try_into_cell(self) -> Result<MemoryCell<'bump>, Self> {
        if let Self::Cell(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    /// Returns `true` if the macro ref is [`Exec`].
    ///
    /// [`Exec`]: MacroRef::Exec
    #[must_use]
    pub fn is_exec(&self) -> bool {
        matches!(self, Self::Exec)
    }
}

impl<'bump, F> From<Option<F>> for MacroRef<'bump>
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
impl<'bump, F> From<F> for MacroRef<'bump>
where
    F: Into<MemoryCell<'bump>>,
{
    fn from(value: F) -> Self {
        Self::Cell(value.into())
    }
}

impl<'bump> From<MacroRef<'bump>> for Option<MemoryCell<'bump>> {
    fn from(val: MacroRef<'bump>) -> Self {
        match val {
            MacroRef::Input | MacroRef::Exec => None,
            MacroRef::Cell(x) => Some(x),
        }
    }
}
