use steel::rvals::FromSteelVal;
use steel_derive::Steel;

#[derive(Debug, Steel)]
#[steel(constructor)]
pub struct Configuration {
    /// Wether to keep the smt files around (or let the os get rid of them once
    /// we're done using them)
    pub keep_smt_files: bool,

    pub depth: u64,
}

impl Default for Configuration {
    fn default() -> Self {
        Self {
            keep_smt_files: false,
            depth: u64::MAX,
        }
    }
}
