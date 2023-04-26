use std::{cell::RefCell, hash::Hash, rc::Rc};

use if_chain::if_chain;
use itertools::Itertools;

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::{forall, meq, RichFormula},
        function::{
            subterm::{self, Subsubterm},
            term_algebra::name::NameCaster,
            Function,
        },
        sort::builtins::{MESSAGE, NONCE},
        utils::formula_expander::DeeperKinds,
        variable::Variable,
    },
    mexists, mforall,
    problem::{
        generator::Generator,
        problem::Problem,
        subterm::{
            kind::SubtermKind,
            traits::{DefaultAuxSubterm, SubtermAux, VarSubtermResult},
            Subterm,
        },
    },
    utils::vecref::VecRef,
};

pub type SubtermEufCmaSignMain<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;
pub type SubtermEufCmaSignKey<'bump> = Subterm<'bump, KeyAux<'bump>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EufCmaSign<'bump> {
    /// mac(Message, Key) -> Signature
    sign: Function<'bump>,
    /// verify(Signature, Message, Key) -> bool
    verify: Function<'bump>,
    /// verify(Key) -> pKey
    pk: Function<'bump>,
}

impl<'bump> EufCmaSign<'bump> {
    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let nonce_sort = NONCE.clone();
        let message_sort = MESSAGE.clone();
        let ev = &pbl.evaluator;
        let nc = &pbl.name_caster;
        let kind = env.into();

        let subterm_main = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_euf_cma_main"),
            kind,
            DefaultAuxSubterm::new(message_sort),
            [],
            DeeperKinds::default(),
            |rc| Subsubterm::EufCmaSignMain(rc),
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_euf_cma_key"),
            kind,
            KeyAux {
                euf_cma: *self,
                name_caster: Rc::clone(&pbl.name_caster),
            },
            [self.sign, self.pk],
            DeeperKinds::NO_MACROS,
            |rc| Subsubterm::EufCmaSignKey(rc),
        );

        if env.preprocess_instances() {
            assertions.extend(
                self.preprocess(pbl, subterm_main.as_ref(), subterm_key.as_ref())
                    .map(Axiom::base),
            )
        }

        if env.define_subterm() {
            define_subterms(
                env,
                pbl,
                assertions,
                declarations,
                &subterm_key,
                &subterm_main,
            );
        }

        if env.with_general_crypto_axiom() && env.define_subterm() {
            let max_var = pbl.max_var() + 1;
            let split = Function::new_spliting(env.container_full_life_time(), [message_sort]);
            declarations.push(Declaration::FreeFunction(split));

            assertions.push(Axiom::base({
                let k = Variable {
                    id: max_var,
                    sort: nonce_sort,
                };
                let k_f = k.into_formula();
                let ors = RichFormula::ors(subterm_key.preprocess_whole_ptcl(&pbl.protocol, &k_f));

                forall([k], split.f([k_f]) >> ors)
            }));

            assertions.push(Axiom::base(
                mforall!(m!1:message_sort, sigma!2:message_sort, k!3:nonce_sort; {
                    let k_f = nc.cast(message_sort, k.clone());
                    ev.eval(self.verify.f([m.clone(), sigma.clone(), self.pk.f([ k_f.clone()])])) >>
                    mexists!(u!4:message_sort; {
                        meq(ev.eval(u.clone()), ev.eval(m.clone())) &
                        (
                            subterm_main.f( self.sign.f([u.clone(), k_f.clone()]), m.clone()) |
                            subterm_main.f( self.sign.f([u.clone(), k_f.clone()]), sigma.clone()) |
                            subterm_key.f( k.clone(), m.clone()) |
                            subterm_key.f( k.clone(), sigma.clone()) |
                            split.f([k])
                        )
                    })
                }),
            ))
        }
    }

    pub fn preprocess<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
        subterm_main: &'a Subterm<'bump, impl SubtermAux<'bump>>,
        subterm_key: &'a Subterm<'bump, impl SubtermAux<'bump>>,
    ) -> impl Iterator<Item = RichFormula<'bump>> + 'a {
        let max_var = pbl.max_var();
        // let pile1 = RefCell::new(Vec::new());
        let pile2 = RefCell::new(Vec::new());
        let candidates = pbl
            .list_top_level_terms()
            .flat_map(move |f| f.iter()) // sad...
            .filter_map(|formula| match formula {
                RichFormula::Fun(fun, args) => {
                    if_chain! {
                        if fun == &self.verify;
                        if let RichFormula::Fun(mpk, args2) = &args[2];
                        if mpk == &self.pk;
                        if let RichFormula::Fun(nf, args3) = &args2[0];
                        if nf == pbl.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                        then {
                            Some(EufCandidate {message: &args[0], signature: &args[1], key: &args3[0]})
                        } else {None}
                    }
                }
                _ => None,
            }).unique()
            .filter_map(move |EufCandidate { message, signature, key }| {
                let array = [message, signature, key];
                let max_var = array.iter()
                    .flat_map(|f| f.used_variables_iter_with_pile(pile2.borrow_mut()))
                    .map(|Variable { id, ..} | *id)
                    .max().unwrap_or(max_var) + 1;
                let free_vars = array.iter()
                    .flat_map(|f| f.get_free_vars().into_iter())
                    .cloned().unique();
                let u_var = Variable {id: max_var, sort: MESSAGE.clone()};
                let u_f = u_var.into_formula();

                let k_sc = subterm_key.preprocess_terms(&pbl.protocol, key,
                    pbl.protocol.list_top_level_terms_short_lifetime()
                        .chain([message, signature].into_iter())
                    , false, DeeperKinds::NO_MACROS).next().is_none();
                if k_sc {
            let disjunction = subterm_main.preprocess_terms(&pbl.protocol, &u_f, [message, signature], true, DeeperKinds::all());

                Some(mforall!(free_vars, {
                    pbl.evaluator.eval(self.verify.f([message.clone(), signature.clone(), self.pk.f([ pbl.name_caster.cast(MESSAGE.clone(), key.clone())])]))
                    >> mexists!([u_var], {
                            RichFormula::ors(disjunction)
                        })
                }))
                } else {None}
            });

        // [].into_iter()
        candidates
    }
}

fn define_subterms<'bump>(
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    subterm_key: &Rc<Subterm<'bump, impl SubtermAux<'bump>>>,
    subterm_main: &Rc<Subterm<'bump, impl SubtermAux<'bump>>>,
) {
    let nonce_sort = NONCE.clone();
    let kind = env.into();
    {
        let subterm = subterm_key.as_ref();
        declarations.push(subterm.declare(pbl));

        if let SubtermKind::Vampire = kind {
        } else {
            assertions.extend(
                subterm
                    .generate_function_assertions_from_pbl(pbl)
                    .into_iter()
                    .chain(
                        subterm.not_of_sort(
                            pbl.sorts.iter().filter(|&&s| s != subterm.sort()).cloned(),
                        ),
                    )
                    .map(|f| Axiom::base(f)),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(pbl, false)
                .map(|f| Axiom::base(f)),
        );
    }
    {
        let subterm = subterm_main.as_ref();
        declarations.push(subterm.declare(pbl));

        if let SubtermKind::Vampire = kind {
        } else {
            assertions.extend(
                subterm
                    .generate_function_assertions_from_pbl(pbl)
                    .into_iter()
                    .chain(
                        subterm.not_of_sort(
                            pbl.sorts.iter().filter(|&&s| s != subterm.sort()).cloned(),
                        ),
                    )
                    .map(|f| Axiom::base(f)),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(pbl, true)
                .map(|f| Axiom::base(f)),
        );
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct EufCandidate<'a, 'bump> {
    message: &'a RichFormula<'bump>,
    signature: &'a RichFormula<'bump>,
    key: &'a RichFormula<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAux<'bump> {
    euf_cma: EufCmaSign<'bump>,
    name_caster: Rc<NameCaster<'bump>>,
}

impl<'bump> SubtermAux<'bump> for KeyAux<'bump> {
    type IntoIter<'a> = VecRef<'a, RichFormula<'bump>>
    where
        'bump: 'a;

    fn sort(&self) -> crate::formula::sort::Sort<'bump> {
        NONCE.clone()
    }

    fn var_eval_and_next<'a>(
        &self,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let nexts = match m {
            RichFormula::Fun(fun, args) => 'function: {
                if_chain! {
                    if fun == &self.euf_cma.sign;
                    if let RichFormula::Fun(nf, args2) = &args[1];
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args2[0]])
                        break 'function VecRef::Vec(vec![&args[0]]) // can't be the subterm of another nonce
                    }
                }
                if_chain! {
                    if fun == &self.euf_cma.pk;
                    if let RichFormula::Fun(nf, args2) = &args[0];
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args[1], &args2[0]])
                        break 'function VecRef::Empty // can't be the subterm of another nonce
                    }
                }
                VecRef::Ref(args)
            }
            _ => VecRef::Empty,
        };

        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: m_sort.is_err() || self.sort() == m_sort.unwrap(),
            nexts,
        }
    }
}

impl<'bump> PartialOrd for KeyAux<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(&self, &other))
    }
}
impl<'bump> Ord for KeyAux<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.euf_cma, &other.euf_cma).then_with(|| {
            Ord::cmp(
                &Rc::as_ptr(&self.name_caster),
                &Rc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for KeyAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.euf_cma.hash(state);
        Rc::as_ptr(&self.name_caster).hash(state);
    }
}

impl<'bump> Generator<'bump> for EufCmaSign<'bump> {
    fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        self.generate(assertions, declarations, env, pbl)
    }
}
