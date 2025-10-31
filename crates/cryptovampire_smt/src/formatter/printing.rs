use super::Term;

// Constants for formatting
const SMALL_EXPRESSION_MAX_LENGTH: usize = 80;
const SPACES_PER_INDENT: usize = 2;

fn format_term_oneline(term: &Term) -> (bool, String) {
    match term {
        Term::Atom(atom, None) => (true, atom.clone()),
        Term::SExpr(terms, None) => {
            let mut parts = Vec::new();
            for t in terms {
                let (ok, s) = format_term_oneline(t);
                if !ok {
                    return (false, String::new());
                }
                parts.push(s);
            }
            (true, format!("({})", parts.join(" ")))
        }
        _ => (false, String::new()),
    }
}

/// Formats a `Term` into a string with a given indent level.
pub fn format_term(term: &Term, indent_level: usize) -> String {
    let indent = " ".repeat(indent_level * SPACES_PER_INDENT);

    // Try to format on a single line
    let (ok, oneline) = format_term_oneline(term);
    if ok && oneline.len() < SMALL_EXPRESSION_MAX_LENGTH {
        return format!("{indent}{oneline}");
    }

    // Format on multiple lines
    match term {
        Term::BlankLine(count) => "\n".repeat(*count),
        Term::Comment(comment) => format!("{indent}{comment}"),
        Term::Atom(atom, None) => format!("{indent}{atom}"),
        Term::Atom(atom, Some(comment)) => format!("{indent}{atom}{comment}"),
        Term::SExpr(terms, attached_comment) => {
            let mut s = format!("{indent}(");

            for (i, t) in terms.iter().enumerate() {
                let first = i == 0;
                if !first {
                    s.push('\n');
                }

                // Special handling for initial comments
                if first {
                    if let Term::Comment(_) = t {
                        s.push('\n');
                    } else if let Term::SExpr(_, _) = t {
                        s.push('\n');
                    }
                }

                if first && t.on_a_single_line() {
                    s.push_str(&format_term(t, 0));
                } else {
                    s.push_str(&format_term(t, indent_level + 1));
                }

                if i == terms.len() - 1
                    && let Term::Atom(_, Some(_)) = t
                {
                    s.push('\n');
                }
            }
            if let Some(attached_comment) = attached_comment {
                s.push_str(&format!("\n{indent}){attached_comment}"));
            } else {
                s.push_str(&format!("\n{indent})"));
            }
            s
        }
    }
}
