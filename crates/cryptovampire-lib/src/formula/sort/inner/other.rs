use utils::string_ref::StrRef;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Other {
    Step,
    Name,
}

impl Other {
    /// Returns `true` if the other is [`Step`].
    ///
    /// [`Step`]: Other::Step
    #[must_use]
    pub fn is_step(&self) -> bool {
        matches!(self, Self::Step)
    }

    /// Returns `true` if the other is [`Name`].
    ///
    /// [`Name`]: Other::Name
    #[must_use]
    pub fn is_name(&self) -> bool {
        matches!(self, Self::Name)
    }

    pub fn name<'a>(&self) -> StrRef<'a> {
        match self {
            Self::Name => "Name",
            Self::Step => "Step",
        }
        .into()
    }

    pub fn list() -> [Self; 2] {
        [Self::Name, Self::Step]
    }
}
