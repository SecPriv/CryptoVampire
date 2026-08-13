use std::fmt::{Debug, Display};

pub enum SExpr<'a> {
    Atom(&'a dyn Display),
    AtomDebug(&'a dyn Debug),
    Group(Vec<Self>),
}

impl<'a> Display for SExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SExpr::Atom(printer) => printer.fmt(f),
            SExpr::AtomDebug(printer) => printer.fmt(f),
            SExpr::Group(sexprs) => {
                write!(f, "(")?;
                for e in sexprs {
                    write!(f, "{e} ")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[allow(dead_code)]
pub struct DebugToDisplay<T>(T);

impl<T: Debug> Display for DebugToDisplay<&T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, T: Debug> From<&'a T> for DebugToDisplay<&'a T> {
    fn from(value: &'a T) -> Self {
        Self(value)
    }
}
