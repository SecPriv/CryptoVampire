use bitflags::bitflags;
use serde::{Deserialize, Serialize};

bitflags! {
  #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
           Hash, Debug, Serialize, Deserialize)]
  pub struct DebugLevel: u32 {
    const RULE = 1 << 0;
    const REBUILDS = 2 << 1;
    const OTHER = 3 << 2;
  }
}

impl Default for DebugLevel {
    fn default() -> Self {
        if cfg!(debug_assertions) {
          DebugLevel::RULE
        } else {
          DebugLevel::empty()
        }
    }
}