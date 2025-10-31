use regex::Regex;

use super::Term;

// Parser result type
type ParseResult<'a> = Result<(Term, &'a str), &'a str>;

// Generic parser functions

fn regex_parser<'a>(pattern: &str, input: &'a str) -> Result<(&'a str, &'a str), &'a str> {
    let re = Regex::new(pattern).unwrap();
    if let Some(mat) = re.find(input) {
        Ok((&input[mat.start()..mat.end()], &input[mat.end()..]))
    } else {
        Err(input)
    }
}

// Specific parser implementations

fn parse_atom(input: &str) -> ParseResult<'_> {
    let patterns = [
        r#"^"((?:""|[^"])*)""#,                        // string
        r"^#x[0-9a-fA-F]+",                            // hexadecimal
        r"^#b[0-1]+",                                  // binary
        r"^(?:0|[1-9][0-9]*)\.[0-9]+",                 // decimal
        r"^(?:0|[1-9][0-9]*)",                         // numeral
        r"^\|[^|\\]*\|",                               // quoted_symbol
        r"^(?![0-9]):?[+\-/*=%?!.$_~&^<>@0-9a-zA-Z]+", // simple_symbol
    ];

    for pattern in &patterns {
        let re = Regex::new(pattern).unwrap();
        if let Some(m) = re.find(input.trim_start()) {
            let atom_str = m.as_str().to_string();
            let remaining = &input.trim_start()[m.end()..];
            let (comment, final_remaining) = parse_raw_comment(remaining).unwrap_or_default();
            return Ok((Term::Atom(atom_str, comment.into()), final_remaining));
        }
    }
    Err(input)
}

fn parse_sexpr(input: &str) -> ParseResult<'_> {
    let trimmed_input = input.trim_start();
    if !trimmed_input.starts_with('(') {
        return Err(input);
    }

    let mut remaining = &trimmed_input[1..];
    let mut terms = Vec::new();

    while let Ok((term, next_input)) = parse_term(remaining) {
        terms.push(term);
        remaining = next_input;
    }

    let trimmed_remaining = remaining.trim_start();
    if !trimmed_remaining.starts_with(')') {
        return Err(input);
    }

    remaining = &trimmed_remaining[1..];
    let (comment, final_remaining) = parse_raw_comment(remaining).unwrap_or_default();
    Ok((Term::SExpr(terms, comment.into()), final_remaining))
}

fn parse_comment(input: &str) -> ParseResult<'_> {
    if let Ok((comment, remaining)) = parse_raw_comment(input.trim_start()) {
        Ok((Term::Comment(comment.into()), remaining))
    } else {
        Err(input)
    }
}

fn parse_raw_comment(input: &str) -> Result<(String, &str), &str> {
    if let Ok((comment, remaining)) = regex_parser(r"^[ \t]*;.*", input) {
        Ok((comment.to_string(), remaining))
    } else {
        Err(input)
    }
}

fn parse_blankline(input: &str) -> ParseResult<'_> {
    let re = Regex::new(r"^(\s*?\n){2,}").unwrap();
    if let Some(m) = re.find(input) {
        let count = m.as_str().chars().filter(|&c| c == '\n').count() - 1;
        let remaining = &input[m.end()..];
        Ok((Term::BlankLine(count), remaining))
    } else {
        Err(input)
    }
}

fn parse_term(input: &str) -> ParseResult<'_> {
    let parsers = [parse_blankline, parse_comment, parse_sexpr, parse_atom];
    for parser in &parsers {
        if let Ok((term, remaining)) = parser(input) {
            return Ok((term, remaining));
        }
    }
    Err(input)
}

/// Parses an SMT-LIB program into a vector of `Term`s.
pub fn parse_program(input: &str) -> Result<Vec<Term>, String> {
    let mut terms = Vec::new();
    let mut remaining = input;
    while !remaining.trim().is_empty() {
        match parse_term(remaining) {
            Ok((term, next_input)) => {
                terms.push(term);
                remaining = next_input;
            }
            Err(e) => {
                return Err(format!(
                    "smtfmt: error: not formatting, leftover: {}",
                    e.trim()
                ));
            }
        }
    }
    Ok(terms)
}
