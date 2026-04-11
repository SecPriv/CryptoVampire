use std::fmt::Display;
use std::path::Path;
use std::time::Duration;

use itertools::Itertools;
use log::trace;
use rustc_hash::FxHashMap;
use steel::steel_vm::builtin::BuiltInModule;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::problem::Function;

#[derive(Debug, Clone, Steel, Default)]
pub struct Report {
    pub(crate) time_spent_in_vampire: Duration,
    pub(crate) max_vampire: Duration,
    pub(crate) total_run_calls: u64,
    pub(crate) total_cache_hits: u64,
    pub(crate) runtime: Duration,
    pub(crate) tested_nonces: Vec<Vec<Function>>,
}

impl Report {
    pub fn get_time_spent_in_vampire(&self) -> Duration {
        self.time_spent_in_vampire
    }

    pub fn get_total_run_calls(&self) -> u64 {
        self.total_run_calls
    }

    pub fn get_total_cache_hits(&self) -> u64 {
        self.total_cache_hits
    }

    pub fn get_hit_rate(&self) -> f64 {
        (self.get_total_cache_hits() as f64) / (self.get_total_run_calls() as f64)
    }

    pub fn get_runtime(&self) -> Duration {
        self.runtime
    }

    pub fn get_tested_nonces(&self) -> Vec<Vec<Function>> {
        self.tested_nonces.clone()
    }

    pub fn add_smt_time(
        &mut self,
        keep_smt_files: bool,
        time: Duration,
        file: Option<&Path>,
        successfull: bool,
    ) {
        self.time_spent_in_vampire += time;

        if successfull && time > self.max_vampire {
            self.max_vampire = time;
            if keep_smt_files {
                println!(
                    "new longest successful vampire:\n\ttook {}\n\tfile saved at {:?}",
                    humantime::format_duration(time),
                    file.unwrap()
                )
            }
        }
    }
}

impl Registerable for Report {
    fn register(modules: &mut FxHashMap<String, BuiltInModule>) {
        let name = "cryptovampire/ll/report";
        let mut module = BuiltInModule::new(name);
        Self::register_type(&mut module);
        module
            .register_fn("get-smt-time", Self::get_time_spent_in_vampire)
            .register_fn("get-total-run-calls", Self::get_total_run_calls)
            .register_fn("get-total-cache-hits", Self::get_total_cache_hits)
            .register_fn("get-hit-rate", Self::get_hit_rate)
            .register_fn("get-runtime", Self::get_runtime)
            .register_fn("get-tested-nonces", Self::get_tested_nonces)
            .register_fn("print-report", Self::to_string);

        trace!("defined {name} scheme module");
        assert!(modules.insert(name.into(), module).is_none())
    }
}

impl Display for Report {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Report:\n\truntime: {}\n\tsmt: {}\n\tcache hits: {:}\n\ttotal calls: {:}\n\thit \
             rate: {:.2}%\n\tmax smt: {}\n\ttested nonces: [{}]",
            humantime::format_duration(self.get_runtime()),
            humantime::format_duration(self.get_time_spent_in_vampire()),
            self.total_cache_hits,
            self.total_run_calls,
            self.get_hit_rate() * 100.0,
            humantime::format_duration(self.max_vampire),
            self.tested_nonces
                .iter()
                .map(|x| format!("[{}]", x.iter().join(", ")))
                .join(", ")
        )
    }
}
