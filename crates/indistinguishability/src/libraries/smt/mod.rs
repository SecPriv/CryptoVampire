use cryptovampire_smt::{Smt, SmtCons, SmtFormula};
use itertools::{Itertools, chain, izip};
use utils::{dynamic_iter, ereturn_if};

use crate::terms::{
    ATT, AliasRewrite, Cryptography, EMPTY, Exists, FROM_BOOL, FindSuchThat, Function, HAPPENS,
    INIT, LEQ, LT, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, PRED, PROJ_1,
    PROJ_2, Quantifier, QuantifierT, Rewrite, SMT_ITE, SMT_SORT_LIST, Signature, Sort, TUPLE,
    UNFOLD_COND, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG,
};
use crate::{MSmt, MSmtFormula, Problem, smt, vec_smt};

pub fn mk_prelude(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    chain![
        mk_header(pbl),
        [MSmt::comment_block("static")],
        mk_base_order(pbl),
        mk_base_macro(pbl),
        mk_base_rewrite(pbl),
        [MSmt::comment_block("term algebra")],
        mk_step_diff(pbl),
        [MSmt::comment_block("Protocol definition")],
        mk_steps_macros(pbl),
        mk_quantifiers(pbl),
        mk_alias(pbl),
        mk_extra_rw(pbl),
        [MSmt::comment_block("Custom")],
        pbl.extra_smt().iter().cloned(),
        [MSmt::comment_block("Cryptography")],
        pbl.cryptography().iter().flat_map(|c| c.mk_prelude(pbl)),
    ]
}

#[inline]
/// Determines if a given function should be declared in the SMT prelude.
///
/// Functions marked as `should_not_declare_in_smt` are excluded.
fn should_declare_in_smt(fun: &Function) -> bool {
    !fun.is_should_not_declare_in_smt()
}

/// Generates the SMT header, including sort and function declarations.
///
/// This includes declarations for built-in sorts, datatypes for nonces and protocols,
/// and functions that are not marked as `should_not_declare_in_smt`.
fn mk_header(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    let sorts = SMT_SORT_LIST.iter().copied().map(Smt::DeclareSort);

    let datatypes = Smt::DeclareDatatypes {
        sorts: vec![Sort::Nonce, Sort::Protocol],
        cons: vec![
            // nonces
            pbl.functions()
                .nonces()
                .map(|f| SmtCons {
                    fun: f.clone(),
                    sorts: f.signature.inputs.clone().into_owned(),
                    dest: vec![None; f.arity()],
                })
                .collect(),
            // protocols
            pbl.functions()
                .protocols()
                .map(|f| SmtCons {
                    fun: f.clone(),
                    sorts: f.signature.inputs.clone().into_owned(),
                    dest: vec![None; f.arity()],
                })
                .collect(),
        ],
    };

    let functions = pbl
        .functions()
        .iter_current()
        .filter(|&x| should_declare_in_smt(x))
        .filter(|x| !x.is_datatype())
        .cloned()
        .map(|fun| {
            let Signature { inputs, output } = &fun.signature;
            Smt::DeclareFun {
                args: inputs.to_vec(),
                out: *output,
                fun,
            }
        });

    chain! {
      sorts,
      [datatypes],
      functions
    }
}

/// Generates SMT assertions for distinctness and injectivity of pseudo-datatypes.
///
/// This ensures that different instances of functions representing datatypes are distinct,
/// and that if two applications of the same function are equal, their arguments must be equal.
// funs are pairwise distincts
fn mk_pseudo_datatype_diff(funs: Vec<Function>) -> impl Iterator<Item = MSmt> {
    let pairs = {
        let mut variables = Vec::with_capacity(funs.iter().map(Function::arity).sum());

        let apps = funs
            .iter()
            .map(|f| {
                let fvars = f.signature.mk_vars();
                variables.extend(fvars.iter().cloned());
                let fvars = fvars.into_iter().map(SmtFormula::Var);
                smt!((f #fvars*))
            })
            .collect_vec();

        smt!((forall #variables (distinct #apps*)))
    };

    // a[veci] = a[vecj] => veci = vecj forall each fun
    let singles = funs.into_iter().filter(|f| f.arity() != 0).map(|f| {
        let v1 = f.signature.mk_vars();
        let v2 = f.signature.mk_vars();
        let vars = chain![&v1, &v2].cloned();
        let and_eq = izip!(&v1, &v2).map(|(v1, v2)| smt!((= #v1 #v2)));
        smt!((forall #vars (=> (= (f #(v1.clone())*) (f #(v2.clone())*)) (and #and_eq*))))
    });

    chain! {
        [pairs], singles
    }
    .map(MSmt::mk_assert)
}

/// Generates SMT assertions for unfolding protocol step macros.
///
/// This iterates through all protocols and their steps, generating SMT rewrites
/// for `UNFOLD_COND`, `UNFOLD_MSG`, `UNFOLD_EXEC`, `UNFOLD_FRAME`, and `UNFOLD_INPUT`.
fn mk_steps_macros(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    pbl.protocols()
        .iter()
        .flat_map(|p| p.steps().iter().map(move |s| (p.as_smt(), s)))
        .flat_map(|(ptcl, s)| s.mk_unfold_vampire_rewrites(pbl, &ptcl))
}

/// Generates SMT assertions to ensure distinctness of protocol steps.
///
/// This uses `mk_pseudo_datatype_diff` to assert that different steps are distinct.
fn mk_step_diff(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    dynamic_iter!(Ret; Empty:A, A:B);

    let steps;
    if let Some(iter) = pbl.steps() {
        steps = iter.collect_vec()
    } else {
        // There are no protocols in this problem
        return Ret::Empty(::std::iter::empty());
    }

    Ret::A(chain! {
        [Smt::Comment("step distinctness".into())],
        mk_pseudo_datatype_diff(steps)
    })
}

/// Generates SMT assertions to ensure distinctness of protocols.
///
/// This uses `mk_pseudo_datatype_diff` to assert that different protocols are distinct.
#[allow(dead_code)]
fn mk_ptcl_diff(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    dynamic_iter!(Ret; Empty:A, A:B);
    let ptcl = pbl.protocols();
    ereturn_if!(ptcl.is_empty(), Ret::Empty(::std::iter::empty()));
    let ptcl = ptcl.iter().map(|p| p.name().clone()).collect();

    Ret::A(chain! {
        [Smt::Comment("protocol distinctiveness".into())],
        mk_pseudo_datatype_diff(ptcl)
    })
}

/// Generates SMT assertions to ensure distinctness of nonces.
///
/// This uses `mk_pseudo_datatype_diff` to assert that different nonces are distinct.
#[allow(dead_code)]
fn mk_nonces_diff(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    use Smt::*;
    let nonces = pbl.functions().nonces().cloned().collect_vec();

    chain! {
        [Comment("nonce distinctness".into())],
        mk_pseudo_datatype_diff(nonces)
    }
}

/// Generates SMT assertions for the basic ordering of time points.
///
/// This includes axioms for `LEQ` (less than or equal), `HAPPENS`, and `PRED` (predecessor).
fn mk_base_order(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    let init = pbl.get_init_fun();
    vec_smt! {%
        ; "order base".into(),
        (forall ((#a Time)) (LEQ (PRED #a) #a)),
        (forall ((#a Time)) (LEQ #a #a)),
        (forall ((#a Time)) (LEQ init #a)),
        (forall ((#a Time) (#b Time)) (=> (and (HAPPENS #a) (LEQ #b #a)) (HAPPENS #b))),
        (forall ((#a Time)) (=> (= (PRED #a) #a) (= #a init))),
        (forall ((#a Time) (#b Time)) (= (LT #a #b) (LEQ #a (PRED #b)))),
        (forall ((#a Time) (#b Time)) (=> (and (HAPPENS #a) (HAPPENS #b)) (or (LEQ #a #b) (LEQ #b #a)))),
        (forall ((#a Time) (#b Time)) (=> (and (LEQ #a #b) (LEQ #b #a)) (= #a #b))),
        (forall ((#a Time) (#b Time) (#c Time)) (=> (and (LEQ #a #b) (LEQ #b #c)) (LEQ #a #c))),
    }.into_iter()
}

/// Generates SMT assertions for unfolding base macros related to protocol execution.
///
/// This includes axioms for `MACRO_COND`, `MACRO_MSG`, `MACRO_EXEC`, `MACRO_FRAME`, and `MACRO_INPUT`.
fn mk_base_macro(_: &Problem) -> impl Iterator<Item = MSmt> {
    vec_smt! {%
        ; "unfold base".into(),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_COND #t #p) (UNFOLD_COND #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_MSG #t #p) (UNFOLD_MSG #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_EXEC #t #p) (UNFOLD_EXEC #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_FRAME #t #p) (UNFOLD_FRAME #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_INPUT #t #p) (UNFOLD_INPUT #t #p)))),
        (forall ((#t Time) (#p Protocol)) (= (UNFOLD_INPUT #t #p) (ATT (MACRO_FRAME (PRED #t) #p)))),
        (forall ((#t Time) (#p Protocol))
            (=> (distinct #t INIT)
                (= (UNFOLD_FRAME #t #p)
                    (TUPLE
                        (TUPLE
                            (FROM_BOOL (MACRO_EXEC #t #p))
                            (SMT_ITE (MACRO_EXEC #t #p)
                                (MACRO_MSG #t #p) EMPTY))
                                (MACRO_FRAME (PRED #t) #p))))),
        (forall ((#t Time) (#p Protocol))
            (=> (distinct #t INIT)
                (= (UNFOLD_EXEC #t #p) (and (MACRO_COND #t #p) (MACRO_EXEC (PRED #t) #p))))),
        (forall ((#p Protocol)) (= (UNFOLD_FRAME INIT #p) (UNFOLD_MSG INIT #p))),
        (forall ((#p Protocol)) (UNFOLD_EXEC INIT #p)),
        (forall ((#t1 Time) (#t2 Time) (#p Protocol))
            (=> (LEQ #t1 #t2) (=> (MACRO_EXEC #t2 #p) (MACRO_EXEC #t1 #p)))),
        (forall ((#t Time)  (#p Protocol))
            (=> (MACRO_EXEC #t #p) (MACRO_COND #t #p))),
    }
    .into_iter()
}

/// Generates SMT assertions for base rewrite rules, such as tuple projections.
fn mk_base_rewrite(_: &Problem) -> impl Iterator<Item = MSmt> {
    vec_smt! {%
        ; "base rewrite".into(),
        (forall ((#m1 Bitstring) (#m2 Bitstring)) (= (PROJ_1 (TUPLE #m1 #m2)) #m1)),
        (forall ((#m1 Bitstring) (#m2 Bitstring)) (= (PROJ_2 (TUPLE #m1 #m2)) #m2))
    }
    .into_iter()
}

/// Generates SMT assertions for quantifiers (Exists and FindSuchThat).
///
/// This iterates through the problem's quantifiers and generates corresponding SMT axioms.
fn mk_quantifiers(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    dynamic_iter!(Tmp; A:A, B:B);
    let ax = pbl
        .functions()
        .current_quantifiers()
        .flat_map(|q| match q {
            Quantifier::Exists(e) => Tmp::A(mk_exists_1(pbl, e)),
            Quantifier::FindSuchThat(e) => Tmp::B(mk_fdst_1(pbl, e)),
        })
        .map(MSmt::mk_assert);

    chain![[MSmt::Comment("quantifiers".into())], ax]
}

/// Generates SMT formulas for an existential quantifier.
///
/// This creates axioms that define the top-level function of the existential
/// and its relationship with the pattern and applied skolem functions.
fn mk_exists_1<'a>(pbl: &'a Problem, e: &'a Exists) -> impl Iterator<Item = MSmtFormula> + use<'a> {
    let all_vars = chain![e.cvars(), e.bvars()].cloned().collect_vec();
    let tlf = e.top_level_function();
    let patt = e.patt().unwrap().as_smt(pbl).unwrap();

    let applied_skolems = e.appplied_skolens().map(|s| s.as_smt(pbl).unwrap());

    vec_smt! {
        (forall #(all_vars.clone()) (= (tlf #(all_vars.clone())*) #(patt))),
        (forall #(all_vars.clone()) (=>
            (tlf #all_vars*) (tlf #(e.cvars())* #(applied_skolems)*)))
    }
    .into_iter()
}

/// Generates SMT formulas for a `FindSuchThat` quantifier.
///
/// This creates axioms that define the top-level function of the `FindSuchThat`
/// and its relationship with the condition, then branch, and else branch.
fn mk_fdst_1<'a>(
    pbl: &'a Problem,
    e: &'a FindSuchThat,
) -> impl Iterator<Item = MSmtFormula> + use<'a> {
    let all_vars = chain![e.cvars(), e.bvars()].cloned().collect_vec();
    let tlf = e.top_level_function();
    let [condition, then_branch, else_branch] =
        [e.condition(), e.then_branch(), e.else_branch()].map(|x| x.unwrap().as_smt(pbl).unwrap());

    let applied_condition = {
        let subst = izip!(e.bvars().iter().cloned(), e.appplied_skolens()).collect_vec();

        e.condition()
            .unwrap()
            .subst(subst.as_slice())
            .as_smt(pbl)
            .unwrap()
    };

    vec_smt! {
        (forall #(all_vars.clone()) (= (tlf #(all_vars.clone())*) (SMT_ITE #condition #then_branch #else_branch))),
        (forall #(all_vars.clone()) (=> #condition #applied_condition))
    }
    .into_iter()
}

/// Generates SMT formulas for a single alias rewrite rule.
///
/// This creates an axiom that equates the `from` and `to` expressions of the alias,
/// universally quantified over the alias's variables.
fn mk_alias_1(
    pbl: &Problem,
    fun: &Function,
    AliasRewrite {
        from,
        to,
        variables,
    }: &AliasRewrite,
) -> impl Iterator<Item = MSmtFormula> {
    let from = from.iter().map(|x| x.as_smt(pbl).unwrap());
    let to = to.as_smt(pbl).unwrap();
    let variables = variables.clone().into_owned();

    [smt!((forall #variables (= (fun #from*) #to)))].into_iter()
}

/// Generates SMT assertions for all aliases defined in the problem.
///
/// This iterates through functions with aliases and generates corresponding SMT axioms
/// using `mk_alias_1`.
fn mk_alias(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    let aliases = pbl
        .functions()
        .iter_current()
        .filter(|x| should_declare_in_smt(x))
        .filter_map(|f| f.alias.as_ref().map(|a| (f, a)))
        .flat_map(|(f, a)| a.0.iter().flat_map(|arw| mk_alias_1(pbl, f, arw)))
        .map(MSmt::mk_assert);

    chain![[MSmt::Comment("aliases".into())], aliases]
}

/// Generates SMT assertions for extra rewrite rules defined in the problem.
///
/// This iterates through rewrite rules that are not prolog-only and generates
/// corresponding SMT axioms.
fn mk_extra_rw(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    let ax = pbl
        .extra_rewrite()
        .iter()
        .filter(|r| !r.prolog_only())
        .map(
            |Rewrite {
                 from,
                 to,
                 variables,
                 ..
             }| {
                let [from, to] = [from, to].map(|x| x.as_smt(pbl).unwrap());
                let vars = variables.clone().into_owned();
                smt!((forall #vars (= #from #to)))
            },
        )
        .map(MSmt::mk_assert);

    chain![[MSmt::Comment("extra rewrites".into())], ax]
}
