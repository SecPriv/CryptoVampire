mod memory_cell;
pub use memory_cell::MemoryCell;

mod assignement;
pub use assignement::Assignement;
use utils::asssert_trait;
use utils::string_ref::StrRef;
use utils::traits::RefNamed;

use crate::container::contained::Containable;
use crate::formula::function::Function;
use crate::formula::sort::Sort;

#[derive(Debug)]
pub struct InnerMemoryCell<'bump> {
    name: String,
    /// the arguments of the cell
    args: Vec<Sort<'bump>>,
    /// the function used to refer to it
    ///
    /// NB: this function takes one more argument of sort step
    function: Function<'bump>,
    /// is accessible iff lock is `Immutable` or using the right lock
    pub assignements: Vec<Assignement<'bump>>,
}

impl<'bump> Eq for InnerMemoryCell<'bump> {}
impl<'bump> PartialEq for InnerMemoryCell<'bump> {
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function && self.name == other.name && self.args == other.args
    }
}
impl<'bump> PartialOrd for InnerMemoryCell<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<'bump> Ord for InnerMemoryCell<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name
            .cmp(&other.name)
            // .then(self.function.cmp(&other.function))
            .then(self.args.cmp(&other.args))
    }
}
impl<'bump> std::hash::Hash for InnerMemoryCell<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.args.hash(state);
        self.function.hash(state);
    }
}

impl<'bump> Containable<'bump> for InnerMemoryCell<'bump> {}

asssert_trait!(sync_send_cell; InnerMemoryCell; Sync, Send);

impl<'bump> InnerMemoryCell<'bump> {
    pub fn new(
        name: String,
        args: Vec<Sort<'bump>>,
        function: Function<'bump>,
        assignements: Vec<Assignement<'bump>>,
    ) -> Self {
        Self {
            name,
            args,
            function,
            assignements,
        }
    }

    pub fn function(&self) -> Function<'bump> {
        self.function
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
}

impl<'a, 'bump: 'a> RefNamed<'a> for &'a InnerMemoryCell<'bump> {
    fn name_ref(&self) -> StrRef<'a> {
        self.name().into()
    }
}
