use std::fs::File;

use parking_lot::ArcMutexGuard;

use crate::Problem;

#[derive(Debug, Default)]
pub struct SinkCache<U> {
    vampire: Option<U>,
    cvc5: Option<U>,
    z3: Option<U>,
}

pub type SmtStringCache = SinkCache<String>;

#[derive(Debug)]
pub struct FileSink {
  cache : ArcMutexGuard<SmtStringCache>,
  file: SinkCache<File>
}

impl SmtStringCache {
    pub fn clear(&mut self) {
        let Self { vampire, cvc5, z3 } = self;

        for x in [vampire, cvc5, z3] {
            if let Some(str) = x {
                str.clear();
            }
        }
    }
}

impl FileSink {
  pub fn new(pbl: &mut Problem) -> Self {
  }
}
