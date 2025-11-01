use std::fmt::Display;

use clap::ValueEnum;
use static_init::dynamic;
use steel_derive::Steel;

use crate::terms::BUILTINS;

#[dynamic]
static CV_PRELUDE: String = {
    let mut mkdefintions: String = "\n".into();

    for f in BUILTINS {
        let name = &f.name;
        let old_name = format!("__pre_{}", f.name);
        mkdefintions += &format!("(define {name} (lift-fun {old_name}))\n");
    }

    include_str!("../../assets/preludes/v1.scm").replace("@@@DEFINITIONS@@@", &mkdefintions)
};

/// Represents the available prelude versions for the cryptovampire tool.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Default, Steel)]
pub enum Preludes {
    V1,
    #[default]
    V2,
}

impl Display for Preludes {
    /// Formats the `Preludes` enum for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::V1 => write!(f, "v1"),
            Self::V2 => write!(f, "v2"),
        }
    }
}

impl Preludes {
    /// Returns the content of the selected prelude as a static string slice.
    pub fn get_prelude(&self) -> &'static str {
        match self {
            Self::V1 => &CV_PRELUDE,
            Self::V2 => include_str!("../../assets/preludes/v2.scm"),
        }
    }
}
