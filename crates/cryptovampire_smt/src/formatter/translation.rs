use std::fmt::Write;

use itertools::izip;

use super::Term;
use crate::{Smt, SmtCons, SmtFormula, SmtParam, SortedVar};

/// Creates a simple S-expression from a list of strings.
/// e.g., `sexpr!["define-fun", "f", "()", "Int"]` becomes `(define-fun f () Int)`
macro_rules! sexpr {
( $( $x:expr ),* ) => {
    {
        Term::sexpr([$( Term::atom($x) ),* ])
    }
};
}
/// Translates an `SmtFormula` into a generic `Term`.
pub fn translate_formula_to_term<U: SmtParam>(formula: &SmtFormula<U>) -> Term {
    match formula {
        SmtFormula::Var(v) => Term::atom(v),
        SmtFormula::True => Term::atom("true"),
        SmtFormula::False => Term::atom("false"),
        SmtFormula::Fun(fun, args) if args.is_empty() => Term::atom(fun),
        SmtFormula::Fun(fun, args) => {
            let mut terms = vec![Term::atom(fun)];
            terms.extend(args.iter().map(translate_formula_to_term));
            Term::SExpr(terms, None)
        }
        SmtFormula::Not(f) => Term::sexpr([Term::atom("not"), translate_formula_to_term(f)]),
        SmtFormula::Implies(f1, f2) => Term::sexpr([
            Term::atom("=>"),
            translate_formula_to_term(f1),
            translate_formula_to_term(f2),
        ]),
        SmtFormula::Ite(i, t, e) => Term::sexpr([
            Term::atom("ite"),
            translate_formula_to_term(i),
            translate_formula_to_term(t),
            translate_formula_to_term(e),
        ]),
        // N-ary operators
        SmtFormula::And(fs) => n_ary_op_to_term("and", fs),
        SmtFormula::Or(fs) => n_ary_op_to_term("or", fs),
        SmtFormula::Eq(fs) => n_ary_op_to_term("=", fs),
        SmtFormula::Neq(fs) => n_ary_op_to_term("distinct", fs),
        // Quantifiers
        SmtFormula::Forall(vars, f) => quantifier_to_term("forall", vars, f),
        SmtFormula::Exists(vars, f) => quantifier_to_term("exists", vars, f),
        // Custom features
        #[cfg(feature = "cryptovampire")]
        SmtFormula::Subterm(_, _, _) => todo!("Translate SmtFormula::Subterm"),
    }
}

/// Helper for n-ary operators like `and`, `or`, `=`, `distinct`.
fn n_ary_op_to_term<U: SmtParam>(op: &str, formulas: &[SmtFormula<U>]) -> Term {
    let mut terms = vec![Term::Atom(op.to_string(), None)];
    terms.extend(formulas.iter().map(translate_formula_to_term));
    Term::SExpr(terms, None)
}

/// Helper for quantifiers `forall` and `exists`.
fn quantifier_to_term<U: SmtParam>(
    quantifier: &str,
    vars: &[U::SVar],
    formula: &SmtFormula<U>,
) -> Term {
    let var_list = Term::sexpr(
        vars.iter()
            .map(|sv| Term::sexpr(vec![Term::atom(&sv), Term::atom(sv.sort_ref())])),
    );
    Term::sexpr([
        Term::atom(quantifier),
        var_list,
        translate_formula_to_term(formula),
    ])
}

/// Translates a top-level `Smt` command into a generic `Term`.
pub fn translate_smt_to_term<U: SmtParam>(smt: &Smt<U>) -> Term {
    match smt {
        Smt::Assert(formula) => {
            Term::sexpr([Term::atom("assert"), translate_formula_to_term(formula)])
        }
        Smt::DeclareFun { fun, args, out } => {
            let arg_sorts = Term::sexpr(args.iter().map(Term::atom));
            Term::sexpr([
                Term::atom("declare-fun"),
                Term::atom(fun),
                arg_sorts,
                Term::atom(out),
            ])
        }
        Smt::DeclareSort(sort) => sexpr!["declare-sort", sort, "0"],
        Smt::DeclareSortAlias { from, to } => sexpr!["define-sort", from, "()", to],
        Smt::DeclareDatatypes { sorts, cons } => {
            let sort_decs = Term::sexpr(sorts.iter().map(|s| sexpr![s, "0"]));

            let cons_decs = Term::sexpr(cons.iter().map(|con_group| {
                Term::sexpr(con_group.iter().map(|SmtCons { fun, sorts, dest }| {
                    let mut c_terms = vec![Term::atom(fun)];
                    c_terms.extend(izip!(dest.iter(), sorts.iter()).enumerate().map(
                        |(i, (sel_name, sel_sort))| match sel_name {
                            Some(sel_name) => sexpr![sel_name, sel_sort],
                            None => sexpr![format!("{fun}$_dest_{i:}"), sel_sort],
                        },
                    ));

                    Term::sexpr(c_terms)
                }))
            }));

            Term::sexpr([Term::atom("declare-datatypes"), sort_decs, cons_decs])
        }
        Smt::Comment(s) => {
            let n = s.chars().filter(|&c| c == '\n').count();
            let mut ret = String::with_capacity(s.len() + 2 * n + 2);

            for s in s.split('\n') {
                writeln!(&mut ret, "; {s}").unwrap();
            }
            Term::Comment(ret)
        }
        Smt::CheckSat => sexpr!["check-sat"],
        Smt::GetProof => sexpr!["get-proof"],
        Smt::SetLogic(logic) => sexpr!["set-logic", logic],
        Smt::SetOption(opt, val) => sexpr!["set-option", format!(":{}", opt), val],

        // Custom features
        #[cfg(feature = "vampire")]
        Smt::AssertTh(formula) => Term::sexpr([
            Term::Comment(
                "; not smt-compliant. Change to `(assert ...)` to be compliant while retaining \
                 the semantics"
                    .into(),
            ),
            Term::atom("assert-theory"),
            translate_formula_to_term(formula),
        ]),
        #[cfg(feature = "vampire")]
        Smt::AssertNot(formula) => Term::sexpr([
            Term::Comment(
                "; not smt-compliant. Change to `(assert (not ...))` to be compliant while \
                 retaining the semantics"
                    .into(),
            ),
            Term::atom("assert-not"),
            translate_formula_to_term(formula),
        ]),

        // todos
        #[cfg(feature = "cryptovampire")]
        Smt::AssertGround { .. } => todo!("Translate Smt::AssertGround"),
        #[cfg(feature = "cryptovampire")]
        Smt::DeclareSubtermRelation(_, _) => todo!("Translate Smt::DeclareSubtermRelation"),
        #[cfg(feature = "cryptovampire")]
        Smt::DeclareRewrite { .. } => todo!("Translate Smt::DeclareRewrite"),
    }
}
