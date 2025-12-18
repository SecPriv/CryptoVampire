use steel_derive::Steel;

#[derive(Debug, Clone, Steel)]
#[steel(contructors)]
pub struct Report {
  time_spent_in_vampire: f64,
  total_run_calls: u64,
  total_cache_hits: u64,
}