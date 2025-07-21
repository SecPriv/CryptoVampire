use cryptovampire_macros::{smt, vec_smt};
use cryptovampire_smt::{Smt, SmtCons, SmtFormula, SortedVar};
use egg::RecExpr;
use itertools::{Itertools, chain, izip};
use logic_formula::egg::SimpleDiscriminant;
use utils::{dynamic_iter, ereturn_if};

use crate::terms::{
    AliasRewrite, Exists, FindSuchThat, Function, Quantifier, QuantifierT, Rewrite, Signature, Sort, ATT, BITE, EMPTY, FROM_BOOL, HAPPENS, LEQ, LT, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, PRED, PROJ_1, PROJ_2, SMT_ITE, SMT_SORT_LIST, TUPLE, UNFOLD_COND, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG
};
use crate::vampire::convert::{formula_to_smt, var_to_smt};
use crate::{MSmt, MSmtFormula, Problem};

pub fn mk_prelude(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    chain![
        mk_header(pbl),
        [MSmt::comment_block("static")],
        mk_base_order(pbl),
        mk_base_macro(pbl),
        mk_base_rewrite(pbl),
        [MSmt::comment_block("term algebra")],
        // mk_nonces_diff(pbl),
        mk_step_diff(pbl),
        // mk_ptcl_diff(pbl),
        [MSmt::comment_block("Protocol definition")],
        mk_steps_macros(pbl),
        mk_quantifiers(pbl),
        mk_alias(pbl),
        mk_extra_rw(pbl),
        [MSmt::comment_block("Custom")],
        pbl.extra_smt().iter().cloned(),
        [MSmt::comment_block("Cryptography")],
        pbl.cryptography().iter().flat_map(|c| c.mk_prelude(pbl))
    ]
}

#[inline]
fn should_declare_in_smt(fun: &Function) -> bool {
    !fun.is_should_not_declare_in_smt()
}

fn mk_header(pbl: &Problem) -> impl Iterator<Item = Smt<Sort, Function>> + use<'_> {
    let sorts = SMT_SORT_LIST.iter().copied().map(Smt::DeclareSort);

    let datatypes = Smt::DeclareDatatypes {
        sorts: vec![Sort::Nonce, Sort::Protocol],
        cons: vec![
            // nonces
            pbl.function
                .nonces()
                .map(|f| SmtCons {
                    fun: f.clone(),
                    sorts: f.signature.inputs.clone().into_owned(),
                    dest: vec![None; f.arity()],
                })
                .collect(),
            // protocols
            pbl.function
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
        .function
        .iter()
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

fn mk_pseudo_datatype_diff(funs: Vec<Function>) -> impl Iterator<Item = MSmt> {
    use SmtFormula::*;

    // funs are pairwise distincts
    let pairs = {
        let mut vars = Vec::with_capacity(funs.iter().map(Function::arity).sum());

        let apps = funs
            .iter()
            .map(|f| {
                let n = vars.len();
                vars.extend(f.signature.mk_sorted_vars(n as u32));
                smt!((f #(vars[n..].iter().cloned())*))
            })
            .collect_vec();

        smt!((forall #vars (distinct #apps*)))
    };

    // a[veci] = a[vecj] => veci = vecj forall each fun
    let singles = funs.into_iter().filter(|f| f.arity() != 0).map(|f| {
        let n = f.arity();
        let svars: Vec<SortedVar<_>> = chain![
            f.signature.mk_sorted_vars(0),
            f.signature.mk_sorted_vars(n as u32)
        ]
        .collect();
        let n1 = smt!((f #(svars[0..n].iter().cloned())*));
        let n2 = smt!((f #(svars[n..2*n].iter().cloned())*));
        let svars_eq = (0..n)
            .map(|i| smt!((= #(Var(svars[i].var.clone())) #(Var(svars[n+i].var.clone())))))
            .collect_vec();
        smt!((forall #svars (=> (= #n1 #n2) (and #svars_eq*))))
    });

    chain! {
        [pairs], singles
    }
    .map(MSmt::mk_assert)
}

fn mk_nonces_diff(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    use Smt::*;
    let nonces = pbl.function.nonces().cloned().collect_vec();

    chain! {
        [Comment("nonce distinctness".into())],
        mk_pseudo_datatype_diff(nonces)
    }
}

fn mk_steps_macros(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    pbl.protocols()
        .iter()
        .flat_map(|p| p.steps().iter().map(move |s| (p.as_smt(), s)))
        .flat_map(|(ptcl, s)| s.mk_unfold_vampire_rewrites(&ptcl))
}

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

fn mk_base_order(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    use crate::terms::Sort::*;
    let init = pbl.get_init_fun();
    let iter = vec_smt! {
        (forall ((#a!0 Time)) (LEQ (PRED #a) #a)),
        (forall ((#a!0 Time)) (LEQ #a #a)),
        (forall ((#a!0 Time)) (LEQ init #a)),
        (forall ((#a!0 Time) (#b!1 Time)) (=> (and (HAPPENS #a) (LEQ #b #a)) (HAPPENS #b))),
        (forall ((#a!0 Time)) (=> (= (PRED #a) #a) (= #a init))),
        (forall ((#a!0 Time) (#b!1 Time)) (= (LT #a #b) (LEQ #a (PRED #b)))),
        (forall ((#a!0 Time) (#b!1 Time)) (=> (and (HAPPENS #a) (HAPPENS #b)) (or (LEQ #a #b) (LEQ #b #a)))),
        (forall ((#a!0 Time) (#b!1 Time)) (=> (and (LEQ #a #b) (LEQ #b #a)) (= #a #b))),
        (forall ((#a!0 Time) (#b!1 Time) (#c!2 Time)) (=> (and (LEQ #a #b) (LEQ #b #c)) (LEQ #a #c))),
    }
    .into_iter()
    .map(Smt::mk_assert);
    chain![[Smt::Comment("order base".into())], iter]
}

fn mk_base_macro(_: &Problem) -> impl Iterator<Item = MSmt> {
    use crate::terms::Sort::*;
    let iter = vec_smt! {
        (forall ((#t!0 Time) (#p!1 Protocol)) (=> (HAPPENS #t) (= (MACRO_COND #t #p) (UNFOLD_COND #t #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol)) (=> (HAPPENS #t) (= (MACRO_MSG #t #p) (UNFOLD_MSG #t #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol)) (=> (HAPPENS #t) (= (MACRO_EXEC #t #p) (UNFOLD_EXEC #t #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol)) (=> (HAPPENS #t) (= (MACRO_FRAME #t #p) (UNFOLD_FRAME #t #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol)) (=> (HAPPENS #t) (= (MACRO_INPUT #t #p) (UNFOLD_INPUT #t #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol)) (= (UNFOLD_INPUT #t #p) (ATT (MACRO_FRAME (PRED #t) #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol))
          (= (UNFOLD_FRAME #t #p)
            (TUPLE
                (TUPLE
                    (FROM_BOOL (MACRO_EXEC #t #p))
                    (SMT_ITE (MACRO_EXEC #t #p)
                        (MACRO_MSG #t #p) EMPTY))
                        (MACRO_FRAME (PRED #t) #p)))),
        (forall ((#t!0 Time) (#p!1 Protocol)) (= (UNFOLD_EXEC #t #p) (and (MACRO_COND #t #p) (MACRO_EXEC (PRED #t) #p))))
    }
    .into_iter()
    .map(Smt::mk_assert);
    chain![[Smt::Comment("unfold base".into())], iter]
}

fn mk_base_rewrite(_: &Problem) -> impl Iterator<Item = MSmt> {
    use crate::terms::Sort::*;
    let iter = vec_smt! {
        (forall ((#m1!0 Bitstring) (#m2!1 Bitstring)) (= (PROJ_1 (TUPLE #m1 #m2)) #m1)),
        (forall ((#m1!0 Bitstring) (#m2!1 Bitstring)) (= (PROJ_2 (TUPLE #m1 #m2)) #m2))
    }
    .into_iter()
    .map(Smt::mk_assert);
    chain![[Smt::Comment("base rewrite".into())], iter]
}

fn mk_quantifiers(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    dynamic_iter!(Tmp; A:A, B:B);
    let ax = pbl
        .function
        .quantifiers()
        .iter()
        .flat_map(|q| match q {
            Quantifier::Exists(e) => Tmp::A(mk_exists_1(e)),
            Quantifier::FindSuchThat(e) => Tmp::B(mk_fdst_1(e)),
        })
        .map(MSmt::mk_assert);

    chain![[MSmt::Comment("quantifiers".into())], ax]
}

fn mk_exists_1(e: &Exists) -> impl Iterator<Item = MSmtFormula> {
    let all_vars = chain![e.cvars_and_sorts(), e.bvars_and_sorts()]
        .map(|(v, s)| SortedVar {
            var: var_to_smt(&v),
            sort: s,
        })
        .collect_vec();
    let cvars = e.cvars_and_sorts().map(|(v, s)| SortedVar {
        var: var_to_smt(&v),
        sort: s,
    });

    let tlf = e.top_level_function();
    let patt = formula_to_smt(e.patt());

    let applied_skolems = e.skolems().iter().map(|sk| smt!((sk #(cvars.clone())*)));

    vec_smt! {
        (forall #(all_vars.clone()) (= (tlf #(all_vars.clone())*) #(patt))),
        (forall #(all_vars.clone()) (=>
            (tlf #all_vars*) (tlf #(cvars.clone())* #(applied_skolems)*)))
    }
    .into_iter()
}

fn mk_fdst_1(e: &FindSuchThat) -> impl Iterator<Item = MSmtFormula> {
    let all_vars = chain![e.cvars_and_sorts(), e.bvars_and_sorts()]
        .map(|(v, s)| SortedVar {
            var: var_to_smt(&v),
            sort: s,
        })
        .collect_vec();

    let tlf = e.top_level_function();
    // let patt = formula_to_smt(e.patt());
    let [condition, then_branch, else_branch] =
        [e.condition(), e.then_branch(), e.else_branch()].map(formula_to_smt);

    let applied_condition = {
        let applied_skolems = e
            .skolems()
            .iter()
            .map(|sk| sk.app_var(&e.cvars_as_lang().map(|x| [x]).collect_vec()));
        let subst = izip!(e.bvars().iter().copied(), applied_skolems).collect_vec();

        let applied_skolems = e
            .condition()
            .iter()
            .cloned()
            .collect::<RecExpr<_>>()
            .apply_pattern_subst(subst);

        formula_to_smt(&applied_skolems)
    };

    vec_smt! {
        (forall #(all_vars.clone()) (= (tlf #(all_vars.clone())*) (SMT_ITE #condition #then_branch #else_branch))),
        (forall #(all_vars.clone()) (=> #condition #applied_condition))
    }
    .into_iter()
}

fn mk_alias_1(
    fun: &Function,
    AliasRewrite {
        from,
        to,
        variables,
        sorts,
    }: &AliasRewrite,
) -> impl Iterator<Item = MSmtFormula> {
    let args = from.iter().map(|x| formula_to_smt(x));
    let content = formula_to_smt(to);
    let vars = izip!(sorts.iter(), variables.iter())
        .map(|(&sort, v)| SortedVar {
            sort,
            var: var_to_smt(v),
        })
        .collect_vec();

    [smt!((forall #vars (= (fun #args*) #content)))].into_iter()
}

fn mk_alias(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    let aliases = pbl
        .function
        .iter()
        .filter(|x| should_declare_in_smt(x))
        .filter_map(|f| f.alias.as_ref().map(|a| (f, a)))
        .flat_map(|(f, a)| a.0.iter().flat_map(|arw| mk_alias_1(f, arw)))
        .map(MSmt::mk_assert);

    chain![[MSmt::Comment("aliases".into())], aliases]
}

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
                 sorts,
                 ..
             }| {
                let [from, to] = [from, to].map(|x| formula_to_smt(x));
                let vars = izip!(sorts.iter(), variables.iter())
                    .map(|(&sort, v)| SortedVar {
                        sort,
                        var: var_to_smt(v),
                    })
                    .collect_vec();
                smt!((forall #vars (= #from #to)))
            },
        )
        .map(MSmt::mk_assert);

    chain![[MSmt::Comment("extra rewrites".into())], ax]
}

#[cfg(test)]
mod test {
    mod basic_hash {
        use itertools::Itertools;

        use crate::vampire::mk_prelude;

        #[test]
        fn prelude() {
            let pbl = crate::problem::test::basic_hash::mk_pblm().0;

            let prelude = mk_prelude(&pbl).collect_vec();

            for x in prelude {
                println!("{x}")
            }
        }
    }
}
