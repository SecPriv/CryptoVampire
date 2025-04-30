mod smt;
pub use smt::{Smt, SmtCons, SmtFile, SmtFormula};

pub const SMT_FILE_EXTENSION: &str = ".smt";

mod sexpr {
    use std::{borrow::Cow, str::FromStr};

    #[derive(Debug, PartialEq)]
    pub enum Sexpr<'a> {
        Atom(Cow<'a, str>),
        List(Vec<Sexpr<'a>>),
    }

    impl<'a> Sexpr<'a> {
        /// Parse a recursive S-expression like "(a (b c) d)"
        pub fn parse(input: &'a str) -> Result<Sexpr<'a>, &'static str> {
            let mut chars = input.trim().chars().peekable();
            parse_sexpr(&mut chars)
        }

        /// Serialize a recursive S-expression
        pub fn serialize(&self) -> String {
            match self {
                Sexpr::Atom(s) => s.to_string(),
                Sexpr::List(items) => {
                    let inner = items
                        .iter()
                        .map(|s| s.serialize())
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("({})", inner)
                }
            }
        }
    }

    /// Helper to skip whitespace
    fn skip_whitespace<I: Iterator<Item = char>>(iter: &mut std::iter::Peekable<I>) {
        while let Some(c) = iter.peek() {
            if c.is_whitespace() {
                iter.next();
            } else {
                break;
            }
        }
    }

    /// Parses an atom or a list
    fn parse_sexpr<'a>(
        chars: &mut std::iter::Peekable<impl Iterator<Item = char>>,
    ) -> Result<Sexpr<'a>, &'static str> {
        skip_whitespace(chars);

        match chars.peek() {
            Some('(') => {
                chars.next(); // consume '('
                let mut items = Vec::new();

                loop {
                    skip_whitespace(chars);
                    if let Some(')') = chars.peek() {
                        chars.next(); // consume ')'
                        break;
                    } else if chars.peek().is_none() {
                        return Err("Unexpected end of input in list");
                    } else {
                        items.push(parse_sexpr(chars)?);
                    }
                }

                Ok(Sexpr::List(items))
            }
            Some(')') => Err("Unexpected ')'"),
            Some(_) => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                Ok(Sexpr::Atom(Cow::Owned(atom)))
            }
            None => Err("Unexpected end of input"),
        }
    }

}
