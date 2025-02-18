#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
pub struct Variable(pub u32);

impl core::fmt::Display for Variable {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "?{:}", self.0)
    }
}

pub mod grammar {
    use anyhow::anyhow;
    use egg::{FromOp, Id, Language, Var};

    use super::Variable;

    #[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
    pub enum Name {
        Str(String),
    }
    impl core::fmt::Display for Name {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Name::Str(n) => write!(f, "{n}"),
            }
        }
    }

    #[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
    pub struct Index(pub u32);

    impl core::fmt::Display for Index {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "#{:}", self.0)
        }
    }

    #[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
    pub enum Op {
        Var(Variable),
        Nonce,
        Name(Name),
        Index(Index),

        Enc,
        Dec,

        Hash,

        Eq,
        IfThenElse,

        Tuple,
        P1,
        P2,

        And,
        Or,
        Not,

        Length,

        Zeroes,
    }

    impl Op {
        pub fn arity(&self) -> usize {
            match self {
                Op::Var(_) => 0,
                Op::Nonce => 1,
                Op::Index(_) => 0,
                Op::Enc => 3,
                Op::Dec => 2,
                Op::Hash => 1,
                Op::Eq => 2,
                Op::IfThenElse => 3,
                Op::Tuple => 2,
                Op::P1 => 1,
                Op::P2 => 1,
                Op::And => 2,
                Op::Or => 2,
                Op::Not => 1,
                Op::Length => 1,
                Op::Zeroes => 1,

                Op::Name(name) => todo!(),
            }
        }
    }

    impl std::str::FromStr for Op {
        type Err = anyhow::Error;

        fn from_str(s: &str) -> anyhow::Result<Self> {
            match s {
                "nonce" => Ok(Self::Nonce),
                "enc" => Ok(Self::Enc),
                "dec" => Ok(Self::Dec),
                "hash" => Ok(Self::Hash),
                "===" | "eq" => Ok(Self::Eq),
                "ite" | "if_then_else" => Ok(Self::IfThenElse),
                "tuple" | "tpl" => Ok(Self::Tuple),
                "p1" | "sel1of2" | "π₁" => Ok(Self::P1),
                "p2" | "sel2of2" | "π₂" => Ok(Self::P2),
                "and" | "&&" | "∧" | "/\\" => Ok(Self::And),
                "or" | "||" | "∨" | "\\/" => Ok(Self::Or),
                "neg" | "not" | "¬" => Ok(Self::Not),
                "length" | "len" => Ok(Self::Length),
                "zeroes" => Ok(Self::Zeroes),
                "" => Err(anyhow!("empty op")),
                x => {
                    let mut chars = x.chars();
                    let det = chars.next().unwrap();
                    let i = chars.as_str();
                    match det {
                        '?' => Ok(Self::Var(Variable(i.parse()?))),
                        '#' => Ok(Self::Index(Index(i.parse()?))),
                        _ => Ok(Self::Name(Name::Str(x.into()))),
                    }
                }
            }
        }
    }

    impl core::fmt::Display for Op {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Op::Var(variable) => variable.fmt(f),
                Op::Nonce => write!(f, "nonce"),
                Op::Name(name) => name.fmt(f),
                Op::Index(index) => index.fmt(f),
                Op::Enc => write!(f, "enc"),
                Op::Dec => write!(f, "dec"),
                Op::Hash => write!(f, "hash"),
                Op::Eq => write!(f, "==="),
                Op::IfThenElse => write!(f, "if_then_else"),
                Op::Tuple => write!(f, "tuple"),
                Op::P1 => write!(f, "π₁"),
                Op::P2 => write!(f, "π₂"),
                Op::And => write!(f, "∧"),
                Op::Or => write!(f, "∨"),
                Op::Not => write!(f, "¬"),
                Op::Length => write!(f, "length"),
                Op::Zeroes => write!(f, "zeroes"),
            }
        }
    }

    #[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
    pub struct TA {
        op: Op,
        args: Vec<Id>,
    }

    impl TA {
        pub fn op(&self) -> &Op {
            &self.op
        }

        pub fn arity(&self) -> usize {
            self.children().len()
        }
    }

    impl Language for TA {
        type Discriminant = Op;
        fn matches(&self, other: &Self) -> bool {
            self.op() == other.op() && self.arity() == other.arity()
        }

        fn children(&self) -> &[Id] {
            &self.args
        }

        fn children_mut(&mut self) -> &mut [Id] {
            &mut self.args
        }

        fn discriminant(&self) -> Self::Discriminant {
            self.op().clone()
        }
    }

    impl FromOp for TA {
        type Error = anyhow::Error;

        fn from_op(op: &str, args: Vec<Id>) -> Result<Self, Self::Error> {
            let op: Op = op.parse()?;
            anyhow::ensure!(op.arity() == args.len(), "arity mishmatch");
            Ok(TA { op, args })
        }
    }
    impl core::fmt::Display for TA {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            self.op().fmt(f)
        }
    }
}
