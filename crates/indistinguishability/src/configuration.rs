use steel_derive::Steel;

#[derive(Debug, Steel)]
#[steel(constructor)]
pub struct Configuration {
    /// Wether to keep the smt files around (or let the os get rid of them once
    /// we're done using them)
    pub keep_smt_files: bool,

    pub depth: u64,

    pub vampire_timeout: f64,
}

impl Default for Configuration {
    fn default() -> Self {
        Self {
            keep_smt_files: cfg!(debug_assertions),
            depth: u64::MAX,
            vampire_timeout: 2f64,
        }
    }
}
