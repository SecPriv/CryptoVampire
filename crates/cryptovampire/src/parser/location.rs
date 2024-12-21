use std::fmt::{Display, Write};

use pest::error::ErrorVariant;

use crate::error::{Locate, LocateHelper, Location, LocationProvider};

#[derive(Debug, Default, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct ASTLocation<'str>(Box<InnerAstLocationHelper<'str>>);

impl<'str> LocateHelper for ASTLocation<'str> {
    fn help_provide(&self, str: &dyn std::fmt::Display) -> Location {
        self.0.help_provide(str)
    }
}

impl<'str> From<pest::Span<'str>> for ASTLocation<'str> {
    fn from(value: pest::Span<'str>) -> Self {
        ASTLocation(Box::new(InnerAstLocationHelper::Span(value)))
    }
}

impl<'str> From<pest::Position<'str>> for ASTLocation<'str> {
    fn from(value: pest::Position<'str>) -> Self {
        ASTLocation(Box::new(InnerAstLocationHelper::Position(value)))
    }
}

impl<'str> ASTLocation<'str> {
    pub fn as_location(&self) -> Location {
        match self.0.as_ref() {
            InnerAstLocationHelper::Span(span) => Location::from_locate(PestLocation::from(*span)),
            InnerAstLocationHelper::Position(position) => {
                Location::from_locate(PestLocation::from(*position))
            }
            // InnerAstLocationHelper::Str(str_ref) => Location::from_locate(str_ref.to_string()),
            _ => Default::default(),
        }
    }

    pub fn all(input: &'str str) -> Self {
        pest::Position::new(input, 0).unwrap().into()
    }
}

impl<'a, 'str> LocationProvider for &'a ASTLocation<'str> {
    fn provide(self) -> Location {
        self.as_location()
    }
}

#[derive(Debug, Default, Hash, PartialEq, Eq, Clone)]
enum InnerAstLocationHelper<'str> {
    Span(pest::Span<'str>),
    Position(pest::Position<'str>),
    // Str(Cow<'str, str>),
    #[default]
    Nothing,
}

impl<'str> LocateHelper for InnerAstLocationHelper<'str> {
    fn help_provide(&self, str: &dyn std::fmt::Display) -> crate::error::Location {
        match self {
            InnerAstLocationHelper::Span(span) => Location::from_locate(PestLocation::from(*span)),
            InnerAstLocationHelper::Position(position) => {
                Location::from_locate(PestLocation::from(*position))
            }
            // InnerAstLocationHelper::Str(str_ref) => str_ref.help_provide(str),
            InnerAstLocationHelper::Nothing => ().help_provide(str),
        }
    }
}

impl<'str> InnerAstLocationHelper<'str> {
    fn int(&self) -> u8 {
        match self {
            InnerAstLocationHelper::Span(..) => 0,
            InnerAstLocationHelper::Position(..) => 1,
            // InnerAstLocationHelper::Str(..) => 2,
            InnerAstLocationHelper::Nothing => 3,
        }
    }
}

impl<'str> PartialOrd for InnerAstLocationHelper<'str> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'str> Ord for InnerAstLocationHelper<'str> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use InnerAstLocationHelper::*;
        match (self, other) {
            (Span(s), Span(s2)) => s
                .as_str()
                .cmp(s2.as_str())
                .then(s.start().cmp(&s2.start()))
                .then(s.end().cmp(&s2.end())),
            (Position(p), Position(p2)) => {
                let s1 = p.span(p);
                let s2 = p2.span(p2);
                s1.as_str()
                    .cmp(s2.as_str())
                    .then(s1.start().cmp(&s2.start()))
            }
            // (Str(s1), Str(s2)) => s1.cmp(s2),
            (x, y) => x.int().cmp(&y.int()),
        }
    }
}

#[derive(Debug, Clone)]
struct PestLocation {
    str: String,
    kind: PestKind,
}

#[derive(Debug, Clone)]
enum PestKind {
    Span { start: usize, end: usize },
    Position { pos: usize },
}

impl Locate for PestLocation {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let mut message = err.to_string();
        if let Some(bcktrc) = backtrace {
            writeln!(message, "\nfrom:\n{bcktrc}")?;
        }
        let variant: ErrorVariant<crate::parser::Rule> =
            pest::error::ErrorVariant::CustomError { message };
        match &self.kind {
            PestKind::Span { start, end } => match pest::Span::new(&self.str, *start, *end) {
                Some(span) => pest::error::Error::new_from_span(variant, span),
                None => {
                    writeln!(f, "!!! FAILED TO BUILD SPAN !!!")?;
                    writeln!(f, "This should not happen, please report")?;
                    writeln!(f, "around {}:{}:{}", file!(), line!(), column!())?;
                    writeln!(f, "start={start:}\nend={end:}")?;
                    writeln!(f, "----error----\n{err}\n----")?;
                    write!(f, "----original's span's content:\n{}", &self.str)?;
                    return Ok(());
                }
            },
            PestKind::Position { pos } => {
                let pos = pest::Position::new(&self.str, *pos)
                    .expect("can't build span (this shouldn't happen)");
                pest::error::Error::new_from_pos(variant, pos)
            }
        }
        .fmt(f)
    }

    fn pseudo_clone(&self) -> Location {
        Location::from_locate(self.clone())
    }
}

impl<'str> From<pest::Span<'str>> for PestLocation {
    fn from(span: pest::Span<'str>) -> Self {
        PestLocation {
            str: span.as_str().into(),
            kind: PestKind::Span {
                start: span.start(),
                end: span.end(),
            },
        }
    }
}

impl<'str> From<pest::Position<'str>> for PestLocation {
    fn from(pos: pest::Position<'str>) -> Self {
        PestLocation {
            str: pos.span(&pos).as_str().into(),
            kind: PestKind::Position { pos: pos.pos() },
        }
    }
}

pub fn all(str: &str) -> Location {
    Location::from_locate(PestLocation::from(pest::Position::new(str, 0).unwrap()))
}

pub trait AsASTLocation<'str> {
    fn ast_location(&self) -> ASTLocation<'str>;
}

impl<'str> AsASTLocation<'str> for pest::iterators::Pair<'str, crate::parser::Rule> {
    fn ast_location(&self) -> ASTLocation<'str> {
        self.as_span().into()
    }
}
