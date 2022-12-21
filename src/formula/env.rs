pub struct Environement {
    pub use_rewrite: bool,
    pub use_special_subterm: bool,
}

impl Default for Environement {
    fn default() -> Self {
        Self {
            use_rewrite: true,
            use_special_subterm: true,
        }
    }
}
