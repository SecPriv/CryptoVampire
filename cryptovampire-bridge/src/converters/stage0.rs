use hashbrown::HashMap;

use crate::json;


pub fn inline_lets<'a>(
    subst: &mut HashMap<json::Term<'a>, json::Term<'a>>,
    t: json::Term<'a>,
) -> json::Term<'a> {
    if let Some(x) = subst.get(&t) {
        x.clone()
    } else {
        use json::Term::*;
        match t {
            App { f, args } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                App { f, args }
            }
            Name { symb, args } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                Name { symb, args }
            }
            Macro {
                symb,
                args,
                timestamp,
            } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                let timestamp = Box::new(inline_lets(subst, *timestamp));
                Macro {
                    symb,
                    args,
                    timestamp,
                }
            }
            Action { symb, args } => {
                let args = args.into_iter().map(|t| inline_lets(subst, t)).collect();
                Action { symb, args }
            }
            Let { var, decl, body } => {
                let old = subst.get(&*var).cloned();
                let decl = inline_lets(subst, *decl);
                subst.insert((*var).clone(), decl);
                let body = inline_lets(subst, *body);
                if let Some(old) = old {
                    subst.insert(*var, old);
                }
                body
            }
            Tuple { elements } => {
                let elements = elements
                    .into_iter()
                    .map(|t| inline_lets(subst, t))
                    .collect();
                Tuple { elements }
            }
            Proj { id, body } => Proj {
                id,
                body: Box::new(inline_lets(subst, *body)),
            },
            Diff { terms } => {
                let terms = terms
                    .into_iter()
                    .map(|json::Diff { proj, term }| json::Diff {
                        proj,
                        term: inline_lets(subst, term),
                    })
                    .collect();
                Diff { terms }
            }
            Find {
                vars,
                condition,
                success,
                faillure,
            } => {
                let [condition, success, faillure] = [condition, success, faillure]
                    .map(|t| inline_lets(subst, *t))
                    .map(Box::new);
                let vars = vars.into_iter().map(|t| inline_lets(subst, t)).collect();
                Find {
                    vars,
                    condition,
                    success,
                    faillure,
                }
            }
            Quant {
                quantificator,
                vars,
                body,
            } => {
                let [body] = [body].map(|t| inline_lets(subst, *t)).map(Box::new);
                let vars = vars.into_iter().map(|t| inline_lets(subst, t)).collect();
                Quant {
                    quantificator,
                    vars,
                    body,
                }
            }
            Var { .. } | Fun { .. } => t,
        }
    }
}