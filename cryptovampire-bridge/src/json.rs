use std::borrow::Cow;

use cryptovampire_lib::formula::variable::uvar;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SquirrelDump<'a, T = Term<'a>, V = Variable<'a>> {
    pub query: Box<T>,
    pub hypotheses: Vec<T>,
    pub variables: Vec<V>,
    #[serde(borrow)]
    pub actions: Vec<Action<'a, T, V>>,
    pub names: Vec<Name<'a>>,
    pub operators: Vec<Operator<'a, T, V>>,
    pub macros: Vec<Macro<'a>>,
    pub types: Vec<Sort<'a>>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Quant {
    ForAll,
    Exists,
    Seq,
    Lambda,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(tag = "constructor")]
pub enum Term<'a> {
    // #[serde(rename_all = "PascalCase")]
    App {
        f: Box<Term<'a>>,
        args: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        symb: Cow<'a, str>,
    },
    // #[serde(rename_all = "PascalCase")]
    Name {
        symb: Cow<'a, str>,
        args: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Macro {
        symb: Cow<'a, str>,
        args: Vec<Term<'a>>,
        timestamp: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Action {
        symb: Cow<'a, str>,
        args: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Var {
        #[serde(flatten, borrow)]
        var: Variable<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    Let {
        var: Box<Term<'a>>,
        decl: Box<Term<'a>>,
        body: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Proj {
        id: u8,
        body: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Diff {
        terms: Vec<Diff<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Find {
        vars: Vec<Term<'a>>,
        condition: Box<Term<'a>>,
        success: Box<Term<'a>>,
        faillure: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Quant {
        quantificator: Quant,
        vars: Vec<Term<'a>>,
        body: Box<Term<'a>>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Diff<'a, T = Term<'a>> {
    pub proj: Cow<'a, str>,
    pub term: T,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Ident<'a> {
    name: Cow<'a, str>,
    tag: i32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Type<'a> {
    Message,
    Boolean,
    Index,
    Timestamp,
    // #[serde(rename_all = "PascalCase")]
    TBase(Cow<'a, str>),
    // #[serde(rename_all = "PascalCase")]
    TVar {
        #[serde(flatten)]
        ident: Ident<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    TUnivar {
        #[serde(flatten)]
        ident: Ident<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Type<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        #[serde(rename = "in")]
        t_in: Box<Type<'a>>,
        out: Box<Type<'a>>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Variable<'a, Ty = Type<'a>> {
    #[serde(borrow)]
    pub id: Ident<'a>,
    #[serde(rename = "ty")]
    pub sort: Box<Ty>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeVariable<'a> {
    #[serde(flatten, borrow)]
    pub id: Ident<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Channel<'a>(Cow<'a, str>);

pub mod action {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Condition<T, V> {
        pub vars: Vec<V>,
        pub term: T,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Ouptut<'a, T> {
        #[serde(borrow)]
        pub channel: Channel<'a>,
        pub term: T,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Update<'a, T> {
        pub symb: Cow<'a, str>,
        pub args: Vec<T>,
        pub body: T,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Item<A> {
        pub par_choice: (u32, A),
        pub sum_choice: (u32, A),
    }

    pub type AT<A> = Vec<Item<A>>;

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Action<'a, T = Term<'a>, V = Variable<'a>> {
        pub name: Cow<'a, str>,
        /// argh... From what I understands this represents the control flow
        /// in a somewhat raw way.
        /// 
        /// The control flow is encoded by layers (the first vec in [AT]).
        /// you have paralell actions ([Item::par_choice]) and exclusive
        /// ones ([Item::sum_choice])
        pub action: AT<Vec<V>>, // this is an `action_v`
        pub input: Channel<'a>,
        pub indices: Vec<V>,
        pub condition: Condition<T, V>,
        #[serde(borrow)]
        pub updates: Vec<Update<'a, T>>,
        pub output: Ouptut<'a, T>,
        pub globals: Vec<Cow<'a, str>>,
    }
}
pub use action::Action;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Content<'a, U> {
    pub symb: Cow<'a, str>,
    pub data: U,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct FunctionType<'a, Ty> {
    #[serde(borrow)]
    pub vars: Vec<TypeVariable<'a>>,
    pub args: Vec<Ty>,
    pub out: Ty,
}

pub type Name<'a, Ty = Type<'a>> = Content<'a, FunctionType<'a, Ty>>;

pub mod operator {
    use std::borrow::Cow;

    use serde::{Deserialize, Serialize};

    use super::*;

    #[allow(non_camel_case_types)]
    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum DhHyp {
        DH_DDH,
        DH_CDH,
        DH_GDH,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum Assoc {
        Right,
        Left,
        NonAssoc,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum SymbType {
        Prefix,
        Infix(Assoc),
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub enum AbstractDef {
        Hash,
        DHgen(Vec<DhHyp>),
        AEnc,
        ADec,
        SEnc,
        SDec,
        Sign,
        CheckSign,
        PublicKey,
        Abstract(SymbType),
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Concrete<'a, T, V, Ty> {
        pub name: Cow<'a, str>,
        #[serde(borrow)]
        pub type_variables: Vec<TypeVariable<'a>>,
        pub args: Vec<V>,
        pub out_type: Ty,
        pub body: T,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    #[serde(untagged)]
    pub enum Def<'a, T, V, Ty> {
        Abstract {
            abstract_def: AbstractDef,
            #[serde(borrow)]
            associated_fun: Vec<Cow<'a, str>>,
        },
        Concrete(Concrete<'a, T, V, Ty>),
    }
    pub type DefaultDef<'a> = Def<'a, Term<'a>, Variable<'a>, Type<'a>>;

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Data<'a, T = Term<'a>, V = Variable<'a>, Ty = Type<'a>> {
        #[serde(rename = "type", borrow)]
        pub sort: FunctionType<'a, Ty>,
        pub def: Def<'a, T, V, Ty>,
    }
}
pub type Operator<'a, T = Term<'a>, V = Variable<'a>, Ty = Type<'a>> =
    Content<'a, operator::Data<'a, T, V, Ty>>;

pub mod mmacro {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub enum Data<Ty> {
        Input,
        Output,
        Cond,
        Exec,
        Frame,
        Global,
        State {
            arity: usize,
            #[serde(rename = "type")]
            sort: Ty,
        },
    }
}
pub type Macro<'a, Ty = Type<'a>> = Content<'a, mmacro::Data<Ty>>;

pub mod mtype {
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum SortKind {
        Large,
        NameFixedLength,
        Finite,
        Fixed,
        WellFounded,
        Enum,
    }

    impl SortKind {
        pub fn can_be_index(&self) -> bool {
            match self{
                SortKind::Finite | SortKind::Fixed | SortKind::Enum => true,
                _ => false
            }
        }
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct SortData(pub Vec<SortKind>);
}
pub type Sort<'a> = Content<'a, mtype::SortData>;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CryptoVampireCall<'a> {
    pub parameters: Parameters,
    #[serde(borrow = "'a")]
    pub context: SquirrelDump<'a>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Parameters {
    pub num_retry: u32,
    pub timeout: f64,
}

#[cfg(test)]
mod tests {
    use paste::paste;
    use std::{
        fs::{self, File},
        io::BufReader,
    };

    use crate::json::action;

    use super::{CryptoVampireCall, SquirrelDump, Term, Type};

    macro_rules! test_json_parser {
        ($f:ident :  $t:ty) => {
            paste! {
                    #[test]
                    fn [<parse_$f>]() {
                        let file_path = format!("tests/assets/squirrel-output/{}.json", stringify!($f));
                        let content = File::open(file_path).expect("Unable to read file");
                        let deserializer = &mut serde_json::Deserializer::from_reader(BufReader::new(content));
                        let result: Result<$t, _> = serde_path_to_error::deserialize(deserializer);
                        result.unwrap();
                    }
                }
        };
    }

    #[test]
    fn types() {
        let t = Type::TBase("LP".into());
        assert_eq!("{\"TBase\":\"LP\"}", &serde_json::to_string(&t).unwrap());
    }

    #[test]
    fn operator_def() {
        use super::operator::*;
        let t = DefaultDef::Abstract {
            abstract_def: AbstractDef::Abstract(SymbType::Infix(Assoc::Right)),
            associated_fun: vec![],
        };
        println!("{}", serde_json::to_string(&t).unwrap());
        assert_eq!(
            "{\"abstract_def\":{\"Abstract\":{\"Infix\":\"Right\"}},\"associated_fun\":[]}",
            &serde_json::to_string(&t).unwrap()
        );
    }

    test_json_parser!(full4:CryptoVampireCall);
    test_json_parser!(term1:Term);
}
