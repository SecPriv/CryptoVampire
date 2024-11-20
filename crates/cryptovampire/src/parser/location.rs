use std::{borrow::Cow, default, fmt::Display};

use utils::string_ref::StrRef;

use crate::error::{Locate, LocateHelper, Location};


#[derive(Debug, Default, Clone)]
pub struct ASTLocation<'str>(Box<InnerAstLocationHelper<'str>>);

impl<'str> LocateHelper for ASTLocation<'str> {
    fn help_provide(&self, str:&dyn std::fmt::Display) -> Location {
        self.0.help_provide(str)
    }
}

impl<'str> From<pest::Span<'str>> for ASTLocation<'str> {
    fn from(value: pest::Span<'str>) -> Self {
        Box::new(InnerAstLocationHelper::Span(value))
    }
}

impl<'str> From<pest::Position<'str>> for ASTLocation<'str> {
    fn from(value: pest::Position<'str>) -> Self {
        Box::new(InnerAstLocationHelper::Position(value))
    }
}

#[derive(Debug, Default, Clone)]
enum InnerAstLocationHelper<'str> {
    Span(pest::Span<'str>),
    Position(pest::Position<'str>),
    Str(Cow<'str, str>),
    #[default]
    Nothing,
}

impl<'str> LocateHelper for InnerAstLocationHelper<'str> {
    fn help_provide(&self, str: &dyn std::fmt::Display) -> crate::error::Location {
        match self {
            InnerAstLocationHelper::Span(span) => Location::from_locate(PestLocation::from(span)),
            InnerAstLocationHelper::Position(position) => {
                Location::from_locate(PestLocation::from(position))
            }
            InnerAstLocationHelper::Str(str_ref) => str_ref.help_provide(str),
            InnerAstLocationHelper::Nothing => ().help_provide(str),
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
        let variant = pest::error::ErrorVariant::CustomError {
            message: err.to_string(),
        };
        match &self.kind {
            PestKind::Span { start, end } => {
                let span = pest::Span::new(&self.str, start, end)
                    .expect("can't build span (this shouldn't happen)");
                pest::error::Error::new_from_span(variant, span)
            }
            PestKind::Position { pos } => {
                let pos = pest::Position::new(&self.str, pos)
                    .expect("can't build span (this shouldn't happen)");
                pest::error::Error::new_from_pos(variant, pos)
            }
        }
        .fmt(f)
    }

    fn pseudo_clone(&self) -> Location {
        Location::from_locate(self.clone());
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
            str: pos.as_str().into(),
            kind: PestKind::Position { pos: pos.pos() },
        }
    }
}

pub fn all(str:&str) -> Location {
    Location::from_locate(PestLocation::from(pest::Position::new(str, 0)));
}