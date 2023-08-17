use std::{cell::RefCell, hash::Hash, sync::Arc};

use if_chain::if_chain;
use itertools::Itertools;

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::{self, forall, meq, ARichFormula, RichFormula},
        function::inner::{subterm::Subsubterm, term_algebra::name::NameCasterCollection},
        function::Function,
        sort::builtins::{CONDITION, MESSAGE, NAME},
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
    static_signature,
    utils::{arc_into_iter::ArcIntoIter, utils::print_type},
};

pub type SubtermEufCmaMacMain<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;
pub type SubtermEufCmaMacKey<'bump> = Subterm<'bump, KeyAux<'bump>>;

static_signature!((pub) EUF_CMA_MAC_SIGNATURE: (MESSAGE, MESSAGE) -> MESSAGE);
static_signature!((pub) EUF_CMA_VERIFY_SIGNATURE: (MESSAGE, MESSAGE, MESSAGE) -> CONDITION);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EufCmaMac<'bump> {
    /// mac(Message, Key) -> Signature
    pub mac: Function<'bump>,
    /// verify(Signature, Message, Key) -> bool
    pub verify: Function<'bump>,
}

impl<'bump> EufCmaMac<'bump> {
    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let nonce_sort = NAME.clone();
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
            |rc| Subsubterm::EufCmaMacMain(rc),
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_euf_cma_key"),
            kind,
            KeyAux {
                euf_cma: *self,
                name_caster: Arc::clone(&pbl.name_caster),
            },
            [self.mac, self.verify],
            DeeperKinds::NO_MACROS,
            |rc| Subsubterm::EufCmaMacKey(rc),
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
                let k_f = k.into_aformula();
                let ors = formula::ors(subterm_key.preprocess_whole_ptcl(&pbl.protocol, &k_f));

                forall([k], split.f_a([k_f]) >> ors)
            }));

            assertions.push(Axiom::base(
                mforall!(m!1:message_sort, sigma!2:message_sort, k!3:nonce_sort; {
                    let k_f = nc.cast(message_sort, k.clone());
                    ev.eval(self.verify.f_a([m.into(), sigma.into(), k_f.clone()])) >>
                    mexists!(u!4:message_sort; {
                        meq(ev.eval(u.clone()), ev.eval(m.clone())) &
                        (
                            subterm_main.f_a( self.mac.f_a([u.into(), k_f.clone()]), m.into()) |
                            subterm_main.f_a( self.mac.f_a([u.into(), k_f.clone()]), sigma.into()) |
                            subterm_key.f_a( k, m) |
                            subterm_key.f_a( k, sigma) |
                            split.f_a([k])
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
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let max_var = pbl.max_var();
        // let pile1 = RefCell::new(Vec::new());
        let pile2 = RefCell::new(Vec::new());
        let candidates = pbl
            .list_top_level_terms()
            .flat_map(move |f| f.iter()) // sad...
            .filter_map(|formula| match formula.as_ref() {
                RichFormula::Fun(fun, args) => {
                    if_chain! {
                        if fun == &self.verify;
                        if let RichFormula::Fun(nf, args2) = args[2].as_ref();
                        if nf == pbl.name_caster.cast_function(&MESSAGE.as_sort()).unwrap();
                        then {
                            Some(EufCandidate {message: args[0].shallow_copy(), signature: args[1].shallow_copy(), key: args2[0].shallow_copy()})
                        } else {None}
                    }
                }
                _ => None,
            }).unique()
            .filter_map(move |EufCandidate { message, signature, key }| {
                let array = [&message, &signature, &key];
                let max_var = array.iter()
                    .flat_map(|f| f.used_variables_iter_with_pile(pile2.borrow_mut()))
                    .map(|Variable { id, ..} | id)
                    .max().unwrap_or(max_var) + 1;
                let free_vars = array.iter()
                    .flat_map(|f| f.get_free_vars().into_iter())
                    // .cloned()
                    .unique();
                let u_var = Variable {id: max_var, sort: MESSAGE.as_sort()};
                let u_f = u_var.into_aformula();

                let k_sc = subterm_key.preprocess_terms(&pbl.protocol, &key,
                    pbl.protocol.list_top_level_terms_short_lifetime()
                        .chain([&message, &signature]).cloned()
                    , false, DeeperKinds::NO_MACROS).next().is_none();
                if k_sc {
            let disjunction = subterm_main.preprocess_terms(&pbl.protocol, &u_f, [&message, &signature].map(|f| f.shallow_copy()), true, DeeperKinds::all());

                Some(mforall!(free_vars, {
                    pbl.evaluator.eval(self.verify.f([message.clone(), signature.clone(), pbl.name_caster.cast( MESSAGE.as_sort(), key.clone())]))
                    >> mexists!([u_var], {
                            formula::ors(disjunction)
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
    subterm_key: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
    subterm_main: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
) {
    let _nonce_sort = NAME.clone();
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

        debug_print::debug_println!("{}:{}:{}", file!(), line!(), column!());

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
        debug_print::debug_println!("{}:{}:{}", file!(), line!(), column!());
        debug_print::debug_println!("subterm type: {}", print_type(subterm));
        debug_print::debug_println!("{}:{}:{}", file!(), line!(), column!());
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(pbl, true)
                .map(|f| Axiom::base(f)),
        );
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct EufCandidate<'bump> {
    message: ARichFormula<'bump>,
    signature: ARichFormula<'bump>,
    key: ARichFormula<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAux<'bump> {
    euf_cma: EufCmaMac<'bump>,
    name_caster: Arc<NameCasterCollection<'bump>>,
}

impl<'bump> SubtermAux<'bump> for KeyAux<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    fn sort(&self) -> crate::formula::sort::Sort<'bump> {
        NAME.clone()
    }

    fn var_eval_and_next(
        &self,
        m: &ARichFormula<'bump>,
    ) -> VarSubtermResult<'bump, Self::IntoIter> {
        let nexts = match m.as_ref() {
            RichFormula::Fun(fun, args) => 'function: {
                if_chain! {
                    if fun == &self.euf_cma.mac;
                    if let RichFormula::Fun(nf, _args2) = args[1].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args2[0]])
                        break 'function [args[0].clone()].into()
                    }
                }
                if_chain! {
                    if fun == &self.euf_cma.verify;
                    if let RichFormula::Fun(nf, _args2) = args[2].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args[1], &args2[0]])
                        break 'function [args[0].clone(), args[1].clone()].into()
                    }
                }
                ArcIntoIter::from(args)
            }
            _ => [].into(),
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
                &Arc::as_ptr(&self.name_caster),
                &Arc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for KeyAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.euf_cma.hash(state);
        Arc::as_ptr(&self.name_caster).hash(state);
    }
}

impl<'bump> Generator<'bump> for EufCmaMac<'bump> {
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
