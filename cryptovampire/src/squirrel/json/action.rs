use super::*;
use itertools::chain;
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

pub type ActionV<'a> = AT<Vec<Variable<'a>>>;

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
    pub action: ActionV<'a>, // this is an `action_v`
    pub input: Channel<'a>,
    pub indices: Vec<Variable<'a>>,
    pub condition: Condition<'a>,
    #[serde(borrow)]
    pub updates: Vec<Update<'a>>,
    pub output: Ouptut<'a>,
    pub globals: Vec<Path<'a>>,
}

impl<'a> Action<'a> {
    pub fn get_args<'b>(&'b self) -> impl Iterator<Item = Term<'a>> + 'b {
        self.action
            .iter()
            .flat_map(
                |Item {
                     par_choice,
                     sum_choice,
                 }| { chain!(par_choice.1.iter(), sum_choice.1.iter()) },
            )
            .map(|v| Term::Var { var: v.clone() })
    }

    /// This is just magic and I don't like it
    /// 
    /// FIXME: understand
    pub fn as_term(&self) -> Term<'a> {
        Term::Action { symb: self.name.clone(), args: self.get_args().collect() }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Shape(AT<usize>);

impl AsRef<AT<usize>> for Shape {
    fn as_ref(&self) -> &AT<usize> {
        &self.0
    }
}

impl<'a> Action<'a> {
    pub fn shape(&self) -> Shape {
        Shape(
            self.action
                .iter()
                .map(
                    |Item {
                         par_choice: (ip, vp),
                         sum_choice: (is, vs),
                     }| {
                        Item {
                            par_choice: (*ip, vp.len()),
                            sum_choice: (*is, vs.len()),
                        }
                    },
                )
                .collect(),
        )
    }
}
