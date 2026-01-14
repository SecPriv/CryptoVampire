use std::fmt::Display;
use std::time::Duration;

use itertools::Itertools;
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
}

impl Registerable for Report {
    fn register(module: &mut BuiltInModule) -> &mut BuiltInModule {
        Self::register_type(module);
        module.register_type::<Duration>("duration?");
        module
            .register_fn("get-time-spent-in-vampire", Self::get_time_spent_in_vampire)
            .register_fn("get-total-run-calls", Self::get_total_run_calls)
            .register_fn("get-total-cache-hits", Self::get_total_cache_hits)
            .register_fn("get-hit-rate", Self::get_hit_rate)
            .register_fn("get-runtime", Self::get_runtime)
            .register_fn("get-tested-nonces", Self::get_tested_nonces)
            .register_fn("print-report", Self::to_string)
    }
}

impl Display for Report {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Report:\n\truntime: {}\n\tvampire: {}\n\tcache hits: {:}\n\ttotal calls: {:}\n\thit \
             rate: {:.2}%\n\tmax vampire: {}\n\ttested nonces: [{}]",
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
