use cryptovampire_smt::{Smt, SmtCons, SmtFormula};
use itertools::{Itertools, chain, izip};
use utils::{econtinue_if, econtinue_let, implvec};

use crate::libraries::utils::{SmtOption, SmtSink};
use crate::libraries::{Cryptography, Library};
use crate::problem::cache::Context;
use crate::terms::{
    ATT, AliasRewrite, EMPTY, Exists, FROM_BOOL, FindSuchThat, Function, HAPPENS, INIT, LEQ, LT,
    MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MEMORY_CELL, MACRO_MSG, PRED, PROJ_1,
    PROJ_2, Quantifier, QuantifierT, Rewrite, SMT_ITE, SMT_SORT_LIST, Signature, Sort, TUPLE,
    UNFOLD_COND, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MEMORY_CELL, UNFOLD_MSG,
};
use crate::{MSmt, MSmtFormula, MSmtParam, Problem, smt, vec_smt};

static SMT_OPTIONS: SmtOption = SmtOption {
    depend_on_context: false,
};

pub struct SmtLib;

impl Library for SmtLib {
    fn add_smt<'a>(&self, pbl: &mut Problem, ctxt: &Context, sink: &mut impl SmtSink<'a>) {
        if ctxt.using_cache {
            add_quantifiers(pbl, sink);
        } else {
            add_header(pbl, sink);

            sink.comment_block(pbl, &SMT_OPTIONS, "static");
            add_base_order(pbl, sink);
            add_base_macro(pbl, sink);
            add_base_rewrite(pbl, sink);

            sink.comment_block(pbl, &SMT_OPTIONS, "term algebra");
            add_step_diff(pbl, sink);

            sink.comment_block(pbl, &SMT_OPTIONS, "Protocol definition");
            add_steps_macros(pbl, sink);
            add_quantifiers(pbl, sink);
            add_alias(pbl, sink);

            sink.comment_block(pbl, &SMT_OPTIONS, "Cryptography");

            pbl.map_cryptography(|pbl, c| {
                c.add_smt(pbl, ctxt, sink);
            });
        }
    }
}

/// Determines if a given function should be declared in the SMT prelude.
///
/// Functions marked as `should_not_declare_in_smt` are excluded.
#[inline]
fn should_declare_in_smt(fun: &Function) -> bool {
    !fun.is_should_not_declare_in_smt()
}

/// Generates the SMT header, including sort and function declarations.
///
/// This includes declarations for built-in sorts, datatypes for nonces and protocols,
/// and functions that are not marked as `should_not_declare_in_smt`.
fn add_header<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    declare_sorts(pbl, sink);
    declare_datatypes(pbl, sink);
    declare_functions(pbl, sink);
}

fn declare_sorts<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.comment(pbl, &SMT_OPTIONS, "declare base sorts");
    sink.extend_smt(
        pbl,
        &SMT_OPTIONS,
        SMT_SORT_LIST.iter().copied().map(Smt::DeclareSort),
    );
}

#[derive(Debug)]
struct Datatype {
    sorts: Vec<Sort>,
    cons: Vec<Vec<SmtCons<MSmtParam>>>,
}

impl<'a> From<Datatype> for MSmt<'a> {
    fn from(Datatype { sorts, cons }: Datatype) -> Self {
        Smt::DeclareDatatypes { sorts, cons }
    }
}

fn declare_one_datatype<'a, 'b>(
    pbl: &Problem,
    sink: &mut impl SmtSink<'b>,
    datatype: &mut Datatype,
    sort: Sort,
    cons: implvec!(&'a Function),
) {
    let cons = cons
        .into_iter()
        .map(|f| SmtCons {
            fun: f.clone(),
            sorts: f.signature.inputs.clone().to_vec(),
            dest: vec![None; f.arity()],
        })
        .collect_vec();

    if cons.is_empty() {
        sink.extend_one_smt(pbl, &SMT_OPTIONS, Smt::DeclareSort(sort));
    } else {
        datatype.sorts.push(sort);
        datatype.cons.push(cons);
    }
}

fn declare_datatypes<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.comment(pbl, &SMT_OPTIONS, "declare datatypes");

    let funs = pbl.functions();
    let mut datatypes = Datatype {
        sorts: Vec::with_capacity(3),
        cons: Vec::with_capacity(3),
    };

    declare_one_datatype(pbl, sink, &mut datatypes, Sort::Protocol, funs.protocols());
    declare_one_datatype(pbl, sink, &mut datatypes, Sort::Nonce, funs.nonces());
    declare_one_datatype(
        pbl,
        sink,
        &mut datatypes,
        Sort::MemoryCell,
        funs.memory_cells(),
    );

    sink.extend_one_smt(pbl, &SMT_OPTIONS, datatypes.into());
}

fn declare_functions<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.comment(pbl, &SMT_OPTIONS, "declare functions");
    for fun in pbl.functions().iter_current() {
        econtinue_if!(!should_declare_in_smt(fun));
        econtinue_if!(fun.is_datatype());
        let Signature { inputs, output } = &fun.signature;
        sink.extend_one_smt(
            pbl,
            &SMT_OPTIONS,
            Smt::DeclareFun {
                args: inputs.clone(),
                out: *output,
                fun: fun.clone(),
            },
        );
    }
}

/// Generates SMT assertions for distinctness and injectivity of pseudo-datatypes.
///
/// This ensures that different instances of functions representing datatypes are distinct,
/// and that if two applications of the same function are equal, their arguments must be equal.
// funs are pairwise distincts
fn add_pseudo_datatype_diff<'a>(pbl: &Problem, funs: Vec<Function>, sink: &mut impl SmtSink<'a>) {
    {
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

        sink.assert_one(
            pbl,
            &SMT_OPTIONS,
            smt!((forall #variables (distinct #apps*))),
        );
    };

    // a[veci] = a[vecj] => veci = vecj forall each fun
    for f in funs {
        econtinue_if!(f.arity() == 0);
        let v1 = f.signature.mk_vars();
        let v2 = f.signature.mk_vars();
        let vars = chain![&v1, &v2].cloned();
        let and_eq = izip!(&v1, &v2).map(|(v1, v2)| smt!((= #v1 #v2)));
        sink.assert_one(
            pbl,
            &SMT_OPTIONS,
            smt!((forall #vars (=> (= (f #(v1.clone())*) (f #(v2.clone())*)) (and #and_eq*)))),
        )
    }
}

/// Generates SMT assertions for unfolding protocol step macros.
///
/// This iterates through all protocols and their steps, generating SMT rewrites
/// for `UNFOLD_COND`, `UNFOLD_MSG`, `UNFOLD_EXEC`, `UNFOLD_FRAME`, and `UNFOLD_INPUT`.
fn add_steps_macros<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    for ptcl in pbl.protocols() {
        let p = ptcl.as_smt();
        for s in ptcl.steps() {
            s.add_unfold_vampire_rewrites(pbl, &p, sink)
        }
    }
}

/// Generates SMT assertions to ensure distinctness of protocol steps.
///
/// This uses `add_pseudo_datatype_diff` to assert that different steps are distinct.
fn add_step_diff<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    let steps;
    if let Some(iter) = pbl.steps() {
        steps = iter.collect_vec()
    } else {
        // There are no protocols in this problem
        return;
    }

    sink.comment(pbl, &SMT_OPTIONS, "step distinctness");
    add_pseudo_datatype_diff(pbl, steps, sink);
}

/// Generates SMT assertions to ensure distinctness of protocols.
///
/// This uses `add_pseudo_datatype_diff` to assert that different protocols are distinct.
#[allow(dead_code)]
fn add_ptcl_diff<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    let ptcl = pbl.protocols();
    if ptcl.is_empty() {
        return;
    }
    let ptcl_funs = ptcl.iter().map(|p| p.name().clone()).collect();

    sink.comment(pbl, &SMT_OPTIONS, "protocol distinctiveness");
    add_pseudo_datatype_diff(pbl, ptcl_funs, sink);
}

/// Generates SMT assertions to ensure distinctness of nonces.
///
/// This uses `add_pseudo_datatype_diff` to assert that different nonces are distinct.
#[allow(dead_code)]
fn add_nonces_diff<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    let nonces = pbl.functions().nonces().cloned().collect_vec();
    sink.comment(pbl, &SMT_OPTIONS, "nonce distinctness");
    add_pseudo_datatype_diff(pbl, nonces, sink);
}

/// Generates SMT assertions for the basic ordering of time points.
///
/// This includes axioms for `LEQ` (less than or equal), `HAPPENS`, and `PRED` (predecessor).
fn add_base_order<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    let init = pbl.get_init_fun();
    sink.extend_smt(pbl, &SMT_OPTIONS, vec_smt! {%
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
    });
}

/// Generates SMT assertions for unfolding base macros related to protocol execution.
///
/// This includes axioms for `MACRO_COND`, `MACRO_MSG`, `MACRO_EXEC`, `MACRO_FRAME`, and `MACRO_INPUT`.
fn add_base_macro<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.extend_smt(pbl, &SMT_OPTIONS, vec_smt! {%
        ; "unfold base".into(),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_COND #t #p) (UNFOLD_COND #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_MSG #t #p) (UNFOLD_MSG #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_EXEC #t #p) (UNFOLD_EXEC #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_FRAME #t #p) (UNFOLD_FRAME #t #p)))),
        (forall ((#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_INPUT #t #p) (UNFOLD_INPUT #t #p)))),
        (forall ((#c MemoryCell) (#t Time) (#p Protocol)) (=> (HAPPENS #t) (= (MACRO_MEMORY_CELL #c #t #p) (UNFOLD_MEMORY_CELL #c #t #p)))),
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
    });
}

/// Generates SMT assertions for base rewrite rules, such as tuple projections.
fn add_base_rewrite<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.extend_smt(
        pbl,
        &SMT_OPTIONS,
        vec_smt! {%
            ; "base rewrite".into(),
            (forall ((#m1 Bitstring) (#m2 Bitstring)) (= (PROJ_1 (TUPLE #m1 #m2)) #m1)),
            (forall ((#m1 Bitstring) (#m2 Bitstring)) (= (PROJ_2 (TUPLE #m1 #m2)) #m2))
        },
    );
}

static SMT_OPTION_QUANTIFIER: SmtOption = SmtOption {
    depend_on_context: true,
};

/// Generates SMT assertions for quantifiers (Exists and FindSuchThat).
///
/// This iterates through the problem's quantifiers and generates corresponding SMT axioms.
fn add_quantifiers<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.comment(pbl, &SMT_OPTION_QUANTIFIER, "quantifiers");
    for q in pbl.cache.smt.occured_quantfiers.borrow().iter() {
        let q = q.get_quantifier(pbl.functions()).unwrap();

        match q {
            Quantifier::Exists(e) => mk_exists_one(pbl, e, sink),
            Quantifier::FindSuchThat(e) => mk_findst_one(pbl, e, sink),
        };
    }
}

fn mk_findst_one<'a>(pbl: &Problem, e: &FindSuchThat, sink: &mut impl SmtSink<'a>) {
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

    sink.assert_many(pbl, &SMT_OPTION_QUANTIFIER, vec_smt! {
        (forall #(all_vars.clone()) (= (tlf #(all_vars.clone())*) (SMT_ITE #condition #then_branch #else_branch))),
        (forall #(all_vars.clone()) (=> #condition #applied_condition))
    })
}

fn mk_exists_one<'a>(pbl: &Problem, e: &Exists, sink: &mut impl SmtSink<'a>) {
    let all_vars = chain![e.cvars(), e.bvars()].cloned().collect_vec();
    let tlf = e.top_level_function();
    let patt = e.patt().unwrap().as_smt(pbl).unwrap();

    let applied_skolems = e.appplied_skolens().map(|s| s.as_smt(pbl).unwrap());

    sink.assert_many(
        pbl,
        &SMT_OPTION_QUANTIFIER,
        vec_smt! {
            (forall #(all_vars.clone()) (= (tlf #(all_vars.clone())*) #(patt))),
            (forall #(all_vars.clone()) (=>
                (tlf #all_vars*) (tlf #(e.cvars())* #(applied_skolems)*)))
        },
    )
}

/// Generates SMT assertions for all aliases defined in the problem.
///
/// This iterates through functions with aliases and generates corresponding SMT axioms.
fn add_alias<'a>(pbl: &Problem, sink: &mut impl SmtSink<'a>) {
    sink.comment(pbl, &SMT_OPTIONS, "aliases");
    for fun in pbl.functions().iter_current() {
        econtinue_if!(!should_declare_in_smt(fun));
        econtinue_let!(let Some(aliases) = fun.alias.as_ref());

        for alias_rewrite in aliases.0.iter() {
            let from_iter: Vec<_> = alias_rewrite
                .from
                .iter()
                .map(|x| x.as_smt(pbl).unwrap())
                .collect();
            let to_formula = alias_rewrite.to.as_smt(pbl).unwrap();
            let vars = alias_rewrite.variables.clone().into_owned();

            sink.assert_one(
                pbl,
                &SMT_OPTIONS,
                smt!((forall #vars (= (fun #from_iter*) #to_formula))),
            );
        }
    }
}

// /// Generates SMT assertions for extra rewrite rules defined in the problem.
// ///
// /// This iterates through rewrite rules that are not prolog-only and generates
// /// corresponding SMT axioms.
// fn add_extra_rw(pbl: &Problem, sink: &mut impl SmtSink<MSmtParam>) {
//     sink.comment("extra rewrites");

//     for Rewrite {
//         from,
//         to,
//         variables,
//         prolog_only,
//         ..
//     } in pbl.extra_rewrite()
//     {
//         econtinue_if!(*prolog_only);
//         let [from, to] = [from, to].map(|x| x.as_smt(pbl).unwrap());
//         let vars = variables.clone().into_owned();
//         sink.assert_one(smt!((forall #vars (= #from #to))))
//     }
// }
