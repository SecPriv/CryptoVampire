use hashbrown::HashSet;
mod tmpformula;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VampireRunner {
    vampire_location: String,
}


/// A possibly thread-safe dump for formulas
#[derive(Debug, Clone)]
pub struct InstanceDump(HashSet<tmpformula::TmpFormula>);
