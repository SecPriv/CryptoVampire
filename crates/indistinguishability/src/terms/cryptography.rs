//! Dumb module to define some of the data regarding cryptopgrahy

use crate::problem::RcRule;


#[derive(Debug)]
pub enum CryptographicAssumption {
    PRF(),
}

impl CryptographicAssumption {
  pub fn get_rules(&self) -> impl Iterator<Item = RcRule> {
    [].into_iter()
  }
}