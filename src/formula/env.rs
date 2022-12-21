use std::collections::HashMap;

use super::{function::Function, sort::Sort};

pub struct Environement {
    pub use_rewrite: bool,
}

impl Default for Environement {
    fn default() -> Self {
        Self { use_rewrite: true }
    }
}
