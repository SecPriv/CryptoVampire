use std::default;

use super::{Location, LocationProvider};

#[derive(Debug)]
pub struct PestLocation {
    input: Box<str>,
    kind: PestKind,
}

#[derive(Debug, Clone, Copy, Default)]
enum PestKind {
    Span { start: usize, end: usize },
    Position { pos: usize },
    #[default]
    All,
}
impl crate::Sealed for PestLocation {}

impl<'a> From<pest::Span<'a>> for PestLocation {
    fn from(value: pest::Span<'a>) -> Self {
        Self {
            input: value.get_input().into(),
            kind: PestKind::Span {
                start: value.start(),
                end: value.end(),
            },
        }
    }
}

impl<'a> From<pest::Position<'a>> for PestLocation {
    fn from(value: pest::Position<'a>) -> Self {
        Self {
            input: value.span(&value).get_input().into(),
            kind: PestKind::Position  {
                pos: value.pos(),
            },
        }
    }
}

impl PestLocation {
    pub fn all(str: &str) -> Self {
      PestLocation { input: str.into(), kind: PestKind::All }
    }

    fn as_pest(&self) -> SpanOrPosition<'_> {
        let input = self.input();
        match self.kind {
            PestKind::Span { start, end } => {
                pest::Span::new(input, start, end).map(SpanOrPosition::Span)
            }
            PestKind::Position { pos } => {
                pest::Position::new(input, pos).map(SpanOrPosition::Position)
            }
            PestKind::All => None,
        }
        .unwrap_or(SpanOrPosition::Position(pest::Position::from_start(
            self.input(),
        )))
    }

    fn input(&self) -> &str {
        &self.input
    }

    fn kind(&self) -> &PestKind {
        &self.kind
    }

    fn into_pest_error<R: pest::RuleType>(
        &self,
        variant: pest::error::ErrorVariant<R>,
    ) -> pest::error::Error<R> {
        match self.as_pest() {
            SpanOrPosition::Span(span) => pest::error::Error::new_from_span(variant, span),
            SpanOrPosition::Position(pos) => pest::error::Error::new_from_pos(variant, pos),
        }
    }
}

enum SpanOrPosition<'a> {
    Span(pest::Span<'a>),
    Position(pest::Position<'a>),
}

impl Location for PestLocation {
    fn location_fmt(err: &crate::Error<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let location = err.get_location();

        let pest_error = match err.get_error() {
            crate::BaseError::PestErrorVariant(variant) => {
                &location.into_pest_error(variant.clone())
            }
            crate::BaseError::PestError(e) => e,
            e => {
                let variant = pest::error::ErrorVariant::<crate::parser::Rule>::CustomError {
                    message: e.to_string(),
                };
                &location.into_pest_error(variant)
            }
        };
        std::fmt::Display::fmt(pest_error, f)?;
        match err.get_backtrace() {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

// impl LocationProvider<Self> for PestLocation {
//     fn provide(self) -> Self {
//         self
//     }
// }