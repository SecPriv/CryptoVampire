use std::fmt::{Display, Write};

use itertools::izip;

use super::Term;
use crate::{Smt, SmtCons, SmtFormula, SortedVar};

/// Creates a simple S-expression from a list of strings.
/// e.g., `sexpr!["define-fun", "f", "()", "Int"]` becomes `(define-fun f () Int)`
macro_rules! sexpr {
( $( $x:expr ),* ) => {
    {
        // let mut temp_vec = Vec::new();
        // $(
        //     temp_vec.push(Term::Atom($x.to_string(), None));
        // )*
        Term::sexpr([$( Term::atom($x) ),* ])
    }
};
}
/// Translates an `SmtFormula` into a generic `Term`.
pub fn translate_formula_to_term<S, F>(formula: &SmtFormula<S, F>) -> Term
where
    S: Display,
    F: Display,
{
    match formula {
        SmtFormula::Var(v) => Term::Atom(v.to_string(), None),
        SmtFormula::True => Term::Atom("true".to_string(), None),
        SmtFormula::False => Term::Atom("false".to_string(), None),
        SmtFormula::Fun(fun, args) => {
            let mut terms = vec![Term::Atom(fun.to_string(), None)];
            terms.extend(args.iter().map(translate_formula_to_term));
            Term::SExpr(terms, None)
        }
        SmtFormula::Not(f) => Term::SExpr(
            vec![
                Term::Atom("not".to_string(), None),
                translate_formula_to_term(f),
            ],
            None,
        ),
        SmtFormula::Implies(f1, f2) => Term::SExpr(
            vec![
                Term::Atom("=>".to_string(), None),
                translate_formula_to_term(f1),
                translate_formula_to_term(f2),
            ],
            None,
        ),
        SmtFormula::Ite(i, t, e) => Term::SExpr(
            vec![
                Term::Atom("ite".to_string(), None),
                translate_formula_to_term(i),
                translate_formula_to_term(t),
                translate_formula_to_term(e),
            ],
            None,
        ),
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
fn n_ary_op_to_term<S, F>(op: &str, formulas: &[SmtFormula<S, F>]) -> Term
where
    S: Display,
    F: Display,
{
    let mut terms = vec![Term::Atom(op.to_string(), None)];
    terms.extend(formulas.iter().map(translate_formula_to_term));
    Term::SExpr(terms, None)
}

/// Helper for quantifiers `forall` and `exists`.
fn quantifier_to_term<S, F>(
    quantifier: &str,
    vars: &[SortedVar<S>],
    formula: &SmtFormula<S, F>,
) -> Term
where
    S: Display,
    F: Display,
{
    let var_list = Term::sexpr(
        vars.iter()
            .map(|sv| Term::sexpr(vec![Term::atom(&sv.var), Term::atom(&sv.sort)])),
    );
    Term::sexpr([
        Term::atom(quantifier),
        var_list,
        translate_formula_to_term(formula),
    ])
}

/// Translates a top-level `Smt` command into a generic `Term`.
pub fn translate_smt_to_term<S, F>(smt: &Smt<S, F>) -> Term
where
    S: Display,
    F: Display,
{
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
                    c_terms.extend(
                        izip!(dest.iter(), sorts.iter())
                            .map(|(sel_name, sel_sort)| sexpr![sel_name, sel_sort]),
                    );

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
