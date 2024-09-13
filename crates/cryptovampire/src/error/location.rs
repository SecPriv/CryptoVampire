#[derive(Debug)]
pub struct OwnedSpan {
    input: Box<str>,
    start: usize,
    end: usize,
}

impl<'a> From<pest::Span<'a>> for OwnedSpan {
    fn from(value: pest::Span<'a>) -> Self {
        Self {
            input: value.get_input().into(),
            start: value.start(),
            end: value.end(),
        }
    }
}

impl OwnedSpan {
    pub fn as_span<'a>(&'a self) -> pest::Span<'a> {
        pest::Span::new(&self.input, self.start, self.end).expect("could not convert to span")
    }
}
