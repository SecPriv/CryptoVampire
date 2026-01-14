use cryptovampire_smt::Smt;
use egg::EGraph;
use golgge::{Program, Rule};
use itertools::Itertools;
use log::trace;

use super::*;
use crate::terms::{EMPTY, EQUIV, HAPPENS, MACRO_FRAME, NONCE, PRED, UNFOLD_MSG};
use crate::{Configuration, Lang, libraries, rexp, smt};

impl Problem {
    /// Build a [Program] to use
    pub fn mk_program<'a>(&'a mut self) -> Program<Lang, PAnalysis<'a>, RcRule> {
        self.state.reset();

        let golgge_config = {
            let Configuration {
                node_limit,
                time_limit,
                iter_limit,
                trace,
                trace_rebuilds,
                ..
            } = self.config;

            let mut gtrace = Default::default();

            if trace {
                gtrace |= golgge::DebugLevel::RULE;
            }
            if trace_rebuilds {
                gtrace |= golgge::DebugLevel::REBUILDS;
            }

            golgge::Config::builder()
                .node_limit(node_limit)
                .iter_limit(iter_limit)
                .time_limit(time_limit)
                .trace(gtrace)
                .build()
        };

        let eq_rules = libraries::mk_egg_rewrites(self);
        let rules: Vec<RcRule> = libraries::mk_golgge_rules(self).collect_vec();

        let mut prgm = golgge::Program::build()
            .eq_rules(eq_rules)
            .rules(rules)
            .config(golgge_config)
            .egraph(EGraph::new(PAnalysis::builder().pbl(self).build()).with_explanations_enabled())
            .call();

        libraries::init_egraph(prgm.egraph_mut());

        prgm
    }

    /// Run the solver on the given protocols
    ///
    /// This function runs the solver on the protocols `p1` and `p2`.
    /// It returns `true` if the protocols are indistinguishable, `false` otherwise.
    ///
    /// # Panics
    ///
    /// This function will panic if `p1` or `p2` are not valid indices for the
    /// protocols in the `Problem`.
    pub fn run_solver(&mut self, p1: usize, p2: usize) -> bool {
        let start = ::std::time::Instant::now();
        assert!(
            p1 < self.protocols.len(),
            "p1 in not a protocol of `self` (index to large)"
        );
        assert!(
            p2 < self.protocols.len(),
            "p2 in not a protocol of `self` (index to large)"
        );
        debug_assert!(self.valid());

        let cp = self.checkpoint();
        // code block to ensure cleanup
        let res = 'a: {
            let res = self.run_solver_internal(p1, p2);
            if res || !self.config.guided_nonce_search {
                break 'a res;
            }

            if self.switch_to_run_public_nonce() {
                loop {
                    let candidates = match &mut self.nonce_finder {
                        NoncePublicSearchState::Run(iter) => iter.next(),
                        _ => unreachable!("switch_to_run_public_nonce ensures we are in Run state"),
                    };

                    let Some(candidates) = candidates else {
                        break 'a false;
                    };

                    if self.config.trace {
                        eprintln!(
                            "re-running with published nonces [{}]",
                            candidates.iter().join(", ")
                        );
                    }

                    self.report.tested_nonces.push(candidates.clone());
                    self.reset_to(&cp);

                    for nonce in candidates {
                        let vars = nonce.args_vars().collect_vec();

                        let term = {
                            let vars = vars.iter().map(|x| x.as_formula());
                            rexp!((NONCE (nonce #vars*)))
                        };

                        self.publish(PublicTerm { vars, term }).unwrap();
                    }

                    let res = self.run_solver_internal(p1, p2);
                    if res {
                        break 'a true;
                    }
                }
            };
            unreachable!()
        };

        self.reset_to(&cp);
        self.report.runtime += start.elapsed();
        res
    }

    /// Run the solver on the given protocols (internal helper)
    fn run_solver_internal(&mut self, p1: usize, p2: usize) -> bool {
        let depth = self.config.depth;
        let base_smt_n = self.extra_smt().len();

        let p1f = self.protocols[p1].name().clone();
        let p2f = self.protocols[p2].name().clone();

        let mut cache_hits = 0;
        let mut total = 0;
        let checkpoint = self.checkpoint();

        // code block to ensure cleanup
        let res = 'a: {
            // the result of the computation
            let mut res = true;

            // the steps in the problem
            let mut steps = {
                // just to make things cleaner
                let get_steps = |i: usize| {
                    self.protocols[i]
                        .steps()
                        .iter()
                        .map(|s| s.id.clone())
                        .collect_vec()
                };

                let steps = get_steps(p1);
                assert!(
                    steps == get_steps(p2),
                    "not the same steps in both protocols!"
                );
                steps.into_iter().enumerate()
            };

            if let Some((idx, init)) = steps.next() {
                debug_assert_eq!(idx, 0);
                self.current_step = Some(CurrentStep { idx, args: vec![] });

                tr!("running input step");
                assert_eq!(init.name, "init");

                // we add to `extra_smt` things specific to this run that need to be reflected in smt
                self.extra_smt_mut()
                    .push(Smt::mk_assert(smt!((HAPPENS init))));

                let mut pgrm = self.mk_program();

                res &= pgrm
                    .run_expr(
                        rexp!((EQUIV EMPTY EMPTY (UNFOLD_MSG init p1f) (UNFOLD_MSG init p2f)))
                            .as_egg_ground(),
                        depth,
                    )
                    .as_bool();

                cache_hits += pgrm.get_memo_hit();
                total += pgrm.get_num_calls();
            } else {
                trace!("empty problem");
                break 'a true;
            }

            for (idx, s) in steps {
                self.reset_to(&checkpoint);

                if !res {
                    // early exists if we failed to prove one result
                    tr!("false!");
                    break 'a res;
                }

                tr!("running step {}", s.name);

                // we ensure we remove the extra stuff from the previous run
                self.extra_smt_mut().truncate(base_smt_n);

                // add and collect functions that will serve as ground indices for the search
                let args = s
                    .signature
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(i, &sort)| {
                        self.declare_function()
                            .output(sort)
                            .fresh_name(format!("{}_{i:}", s.name))
                            .temporary()
                            .call()
                    })
                    .collect_vec();

                self.current_step = Some(CurrentStep {
                    idx,
                    args: args.clone(),
                });

                self.extra_smt.push(Smt::mk_assert({
                    let args = args.iter().map(|f| smt!(f));
                    smt!((HAPPENS (s #args*)))
                }));

                let s = rexp!((s #(args.iter().map(|f| rexp!(f)))*));
                let goal = rexp!((EQUIV (MACRO_FRAME (PRED #s) p1f) (MACRO_FRAME (PRED #s) p2f)
                (MACRO_FRAME #s p1f) (MACRO_FRAME #s p2f)))
                .as_egg_ground();

                let mut pgrm = self.mk_program();

                res &= pgrm.run_expr(goal, depth).as_bool();

                cache_hits += pgrm.get_memo_hit();
                total += pgrm.get_num_calls();
            }
            res
        };

        self.reset_to(&checkpoint);

        self.report.total_cache_hits += cache_hits;
        self.report.total_run_calls += total;

        res
    }
}
