use super::*;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Condition<'a> {
    #[serde(borrow)]
    pub vars: Vec<Variable<'a>>,
    pub term: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Ouptut<'a> {
    #[serde(borrow)]
    pub channel: Channel<'a>,
    pub term: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Update<'a> {
    #[serde(borrow)]
    pub symb: Symb<'a>,
    pub args: Vec<Term<'a>>,
    pub body: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Item<A> {
    pub par_choice: (u32, A),
    pub sum_choice: (u32, A),
}

pub type AT<A> = Vec<Item<A>>;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Action<'a> {
    #[serde(borrow)]
    pub name: Path<'a>,
    /// argh... From what I understands this represents the control flow
    /// in a somewhat raw way.
    ///
    /// The control flow is encoded by layers (the first vec in [AT]).
    /// you have paralell actions ([Item::par_choice]) and exclusive
    /// ones ([Item::sum_choice])
    pub action: AT<Vec<Variable<'a>>>, // this is an `action_v`
    pub input: Channel<'a>,
    pub indices: Vec<Variable<'a>>,
    pub condition: Condition<'a>,
    #[serde(borrow)]
    pub updates: Vec<Update<'a>>,
    pub output: Ouptut<'a>,
    pub globals: Vec<Path<'a>>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Shape(AT<u32>);
