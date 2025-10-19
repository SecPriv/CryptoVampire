// QUESTION: Should we cross reference existential quantifiers?

use FOBinder::{Exists, FindSuchThat};
use QuantifierKindRule::{BothSides, OneSide};
use Side::{Left, Right};
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::izip;
use utils::{ebreak_if, ebreak_let, ereturn_let};

use crate::problem::{PAnalysis, PRule, RcRule};
use crate::terms::{
    BIT_DEDUCE, BOOL_DEDUCE, CONS, EXISTS, FIND_SUCH_THAT, FOBinder, INDEX_SORT, LAMBDA_LET, Sort,
    Variable,
};
use crate::{Lang, Problem, fresh, rexp};

declare_trace!($"quantifier_deduce");

pub fn mk_rules(_: &Problem) -> impl Iterator<Item = RcRule> {
    [Exists, FindSuchThat]
        .map(|quantifier| {
            let (patterns, return_patterns) = QuantifierRule::mk_patterns(quantifier);
            QuantifierRule {
                quantifier,
                patterns,
                return_patterns,
            }
        })
        .map(|x| x.into_mrc())
        .into_iter()
}

/// which side the quantifier is on
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuantifierKindRule {
    BothSides,
    OneSide(Side),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QuantifierRule {
    quantifier: FOBinder,
    patterns: [Pattern<Lang>; 3],
    return_patterns: [Pattern<Lang>; 3],
}

macro_rules! mk_vars {
    ($($n:ident),*) => {
        /// The parameters of a quantifier rule
        #[derive(Debug, Clone)]
        struct Parameters<U = Id> {
            $(
                $n: U
            ),*
        }

        static DEFAULT_PARAMERTERS : Parameters<Variable> = Parameters {$($n: fresh!(const)),*};

        impl Parameters<Variable> {
            #[allow(dead_code)]
            fn all_params(&self) -> impl Iterator<Item = &Variable> {
                [ $(&self.$n),* ].into_iter()
            }
        }

        impl<U> FromIterator<U> for Parameters<U> {
            fn from_iter<T: IntoIterator<Item =U>>(iter: T) -> Self {
                let mut iter = iter.into_iter();
                $( let $n = iter.next().unwrap(); )*
                Parameters { $($n),* }
            }
        }
    };
}

mk_vars!(
    u, v, h1, h2, args1_1, args1_2, args1_3, args2_1, args2_2, args2_3, sort, sort1_cons,
    sort2_cons, other, new_var
);

impl<'a> Rule<Lang, PAnalysis<'a>> for QuantifierRule {
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: egg::Id) -> Dependancy {
        let matches =
            izip!(self.patterns.iter(), self.return_patterns.iter()).find_map(|(pattern, ret)| {
                let matches = pattern.search_eclass(prgm.egraph(), goal)?;
                Some((ret, matches))
            });
        ereturn_let!(let Some((ret, matches)) = matches, Dependancy::impossible());
        #[cfg(debug_assertions)]
        {
            let g = prgm.egraph().id_to_expr(goal);
            tr!("quantifier deduce with: {}", g)
        }

        

        let new_var = prgm
            .egraph_mut()
            .analysis
            .pbl_mut()
            .declare_function()
            .output(Sort::Index)
            .fresh_name("idx")
            .call();
        let new_var = prgm.egraph_mut().add(Lang::new(new_var, []));
        matches
            .substs
            .into_iter()
            .map(|mut subst| {
                'out: { // checks that the sort matches with the new variable
                    'err: {
                        ebreak_let!('err, let Some(&sid) = subst.get(DEFAULT_PARAMERTERS.sort.as_egg()));
                        ebreak_if!('out, prgm.egraph()[sid].nodes[0].head == INDEX_SORT);
                        log::error!("wrong sort: {}", &prgm.egraph()[sid].nodes[0].head);
                    }
                    panic!("only Index is supported in deduce quantifiers")
                }
                subst.insert(DEFAULT_PARAMERTERS.new_var.as_egg(), new_var);
                [ret.apply_susbt(prgm.egraph_mut(), &subst)]
            })
            .collect()
    }

    fn name(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed(match self.quantifier {
            Exists => "quantifier deduce rule (exists)",
            FindSuchThat => "quantifier deduce rule (find)",
            _ => unimplemented!(),
        })
    }
}

impl<U> Parameters<U> {
    fn can_be_ignored(&self, q: FOBinder, kind: QuantifierKindRule) -> Vec<&U> {
        let Parameters {
            args1_2,
            args1_3,
            args2_1,
            args2_2,
            args2_3,
            sort2_cons,
            other,
            new_var,
            ..
        } = self;
        match (q, kind) {
            (Exists, OneSide(_)) => vec![args1_3, args2_1, args2_2, args2_3, sort2_cons, new_var],
            (Exists, BothSides) => vec![args1_2, args1_3, args2_2, args2_3, other, new_var],
            (FindSuchThat, OneSide(_)) => {
                vec![args2_1, args2_2, args2_3, sort2_cons, new_var]
            }
            (FindSuchThat, BothSides) => vec![other, new_var],
            _ => unreachable!(),
        }
    }
}

impl QuantifierRule {
    const fn kind_order() -> &'static [QuantifierKindRule; 3] {
        &[BothSides, OneSide(Left), OneSide(Right)]
    }

    fn assign_subst(&self, kind: QuantifierKindRule, subst: &egg::Subst) -> Parameters {
        let to_ignore = DEFAULT_PARAMERTERS.can_be_ignored(self.quantifier, kind);
        DEFAULT_PARAMERTERS
            .all_params()
            .map(
                |var| match (subst.get(var.as_egg()), to_ignore.contains(&var)) {
                    (None, true) => Id::from(0),
                    (Some(id), false) => *id,
                    _ => unreachable!("doesn't match the pattern"),
                },
            )
            .collect()
    }

    fn mk_patterns(bind: FOBinder) -> ([Pattern<Lang>; 3], [Pattern<Lang>; 3]) {
        let Parameters {
            u,
            v,
            h1,
            h2,
            args1_1,
            args1_2,
            args1_3,
            args2_1,
            args2_2,
            args2_3,
            sort,
            sort1_cons,
            sort2_cons,
            other,
            new_var,
            ..
        } = &DEFAULT_PARAMERTERS;
        let deduce_m = &BIT_DEDUCE;
        let deduce_b = &BOOL_DEDUCE;
        let capture_pattern = match bind {
            FOBinder::Forall => unreachable!(),
            Exists => [
                rexp!((deduce_b #u #v
                    (EXISTS (CONS #sort #sort1_cons) #args1_1)
                    (EXISTS (CONS #sort #sort2_cons) #args2_1)
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    (EXISTS (CONS #sort #sort1_cons) #args1_1)
                    #other
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    #other
                    (EXISTS (CONS #sort #sort1_cons) #args1_1)
                    #h1 #h2)),
            ],
            FindSuchThat => [
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT (CONS #sort #sort1_cons) #args1_1 #args1_2 #args1_3)
                    (FIND_SUCH_THAT (CONS #sort #sort2_cons) #args2_1 #args2_2 #args2_3)
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT (CONS #sort #sort1_cons) #args1_1 #args1_2 #args1_3)
                    #other
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    #other
                    (FIND_SUCH_THAT (CONS #sort #sort1_cons) #args1_1 #args1_2 #args1_3)
                    #h1 #h2)),
            ],
        }
        .map(|x| Pattern::from(&x));
        let return_pattern = match bind {
            FOBinder::Forall => unreachable!(),
            Exists => [
                rexp!((deduce_b #u #v
                    (EXISTS #sort1_cons (LAMBDA_LET #new_var #args1_1))
                    (EXISTS #sort2_cons (LAMBDA_LET #new_var #args2_1))
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    (EXISTS #sort1_cons (LAMBDA_LET #new_var #args1_1))
                    #other
                    #h1 #h2)),
                rexp!((deduce_b #u #v
                    #other
                    (EXISTS #sort1_cons (LAMBDA_LET #new_var #args1_1))
                    #h1 #h2)),
            ],
            FindSuchThat => [
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT #sort1_cons
                        (LAMBDA_LET #new_var #args1_1) (LAMBDA_LET #new_var #args1_2) #args1_3)
                    (FIND_SUCH_THAT #sort2_cons
                        (LAMBDA_LET #new_var #args2_1) (LAMBDA_LET #new_var #args2_2) #args2_3)
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    (FIND_SUCH_THAT #sort1_cons
                        (LAMBDA_LET #new_var #args1_1) (LAMBDA_LET #new_var #args1_2) #args1_3)
                    #other
                    #h1 #h2)),
                rexp!((deduce_m #u #v
                    #other
                    (FIND_SUCH_THAT #sort1_cons
                        (LAMBDA_LET #new_var #args1_1) (LAMBDA_LET #new_var #args1_2) #args1_3)
                    #h1 #h2)),
            ],
        }
        .map(|x| Pattern::from(&x));
        // tr!("{capture_pattern}\n{return_pattern}")
        (capture_pattern, return_pattern)
    }
}

// Generate the rule for a single quantifier
// Funilly enough it's the same thing for exists and fdst
// fn mk_quantifier_deduce_rules_one<Q: QuantifierT>(_pbl: &Problem, e: &Q) -> PrologRule<Lang> {
//     let deduce = e.top_level_function().get_deduce();
//     let max_var: u32 = chain![e.cvars(), e.bvars()]
//         .flat_map(|v| v.as_u32())
//         .max()
//         .unwrap_or(0)
//         + 1;

//     // initiate the variables
//     let [u, v, h1, h2] = ::std::array::from_fn(|i| [ENodeOrVar::Var(Var::from_usize(i as u32))]);
//     let base_vars_n = 4;

//     // u, v |> exits(vecx, vecsk(vecx)), exists(vecy, vecsk(vecy)) # h1, h2
//     let input = {
//         let mk_applied = |start: u32| {
//             let cvars = e
//                 .cvars()
//                 .iter()
//                 .map(|&v| offset::var(start, v))
//                 .map(|v| vec![ENodeOrVar::Var(v)].into())
//                 .collect_vec();
//             let bvars = e.skolems().iter().map(|f| f.app_var(&cvars)).collect_vec();
//             let args = chain![cvars, bvars].collect_vec();
//             e.top_level_function().app_var(&args)
//         };

//         let left = mk_applied(base_vars_n);
//         let right = mk_applied(base_vars_n + max_var);
//         deduce.app_var(
//             &chain![
//                 [u.as_slice(), v.as_slice()],
//                 [left.deref(), right.deref()],
//                 [h1.as_slice(), h2.as_slice()]
//             ]
//             .collect_vec(),
//         )
//     };

//     // u, v |> exits(vecx, vecfresh), exists(vecy, vecfresh) # h1, h2
//     let dep = {
//         let mk_fresh = |start: u32| {
//             let cvars = e
//                 .cvars()
//                 .iter()
//                 .map(|&v| offset::var(start, v))
//                 .map(|v| vec![ENodeOrVar::Var(v)].into())
//                 .collect_vec();
//             let bvars = e
//                 .fresh_indices()
//                 .iter()
//                 .map(|f| f.app_empty_var())
//                 .collect_vec();
//             let args = chain![cvars, bvars].collect_vec();
//             e.top_level_function().app_var(&args)
//         };

//         let left = mk_fresh(base_vars_n);
//         let right = mk_fresh(base_vars_n + max_var);
//         deduce.app_var(
//             &chain![
//                 [u.as_slice(), v.as_slice()],
//                 [left.deref(), right.deref()],
//                 [h1.as_slice(), h2.as_slice()]
//             ]
//             .collect_vec(),
//         )
//     };

//     PrologRule {
//         input: Pattern::from(input),
//         deps: vec![Pattern::from(dep)],
//         cut: false,
//         require_decrease: false,
//         name: Some(format!("deduce {}", e.top_level_function().name)),
//     }
// }
