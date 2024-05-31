use hashbrown::HashSet;
mod tmpformula;
mod vampire_runner;


/// A possibly thread-safe dump for formulas
#[derive(Debug, Clone)]
pub struct InstanceDump(HashSet<tmpformula::TmpFormula>);
