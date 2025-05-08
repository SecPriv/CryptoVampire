use std::{fmt::Debug, hash::Hash, rc::Rc, str::FromStr, sync::atomic::AtomicU32};

use anyhow::anyhow;
use egg::{FromOp, Id, Language, Symbol};
use utils::{impossible::Impossible, match_as_trait};

pub trait InnerLang: FromStr + Debug + Clone + Eq + Hash + Ord {
    fn arity(&self) -> Option<usize>;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Symbols<L, Q, P> {
    BaseTA(L),
    Quant(Q),
    Predicate(P),
    Var(u32),
    Other(Symbol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(u32);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lang<U> {
    symb: U,
    args: Vec<Id>,
}

impl<U> Lang<U> {
    pub fn arity(&self) -> usize {
        self.args.len()
    }
}

impl<U: InnerLang> Lang<U> {
    pub fn mk_app(symb: U, args: Vec<Id>) -> anyhow::Result<Self> {
        match symb.arity() {
            Some(arr) if arr != args.len() => Err(anyhow!(
                "wrong number of arguments (got {:} expected {:})",
                args.len(),
                arr
            )),
            _ => Ok(Self { symb, args }),
        }
    }
}

impl<L, Q, P> Symbols<L, Q, P> {
    pub fn from_ta(l: L) -> Self {
        Self::BaseTA(l)
    }
    pub fn from_quant(q: Q) -> Self {
        Self::Quant(q)
    }
    pub fn from_predicate(p: P) -> Self {
        Self::Predicate(p)
    }
    pub fn fresh_var() -> Self {
        let v = FRESH_VARS_COUNT.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
        assert_ne!(
            v,
            u32::MAX,
            "you ran out of variables (and probably memeory ^^')"
        );
        Symbols::Var(v)
    }
}

impl<U> Language for Lang<U>
where
    U: Debug + Clone + Eq + Hash + Ord,
{
    type Discriminant = U;

    fn discriminant(&self) -> Self::Discriminant {
        self.symb.clone()
    }

    fn matches(&self, other: &Self) -> bool {
        self.discriminant() == other.discriminant() && self.arity() == other.arity()
    }

    fn children(&self) -> &[Id] {
        &self.args
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.args
    }
}

impl<L, Q, P> FromStr for Symbols<L, Q, P>
where
    L: InnerLang,
    Q: InnerLang,
    P: InnerLang,
{
    type Err = Impossible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok((Var::from_str(s).map(Self::from))
            .or_else(|_| L::from_str(s).map(Self::from_ta))
            .or_else(|_| Q::from_str(s).map(Self::from_quant))
            .or_else(|_| P::from_str(s).map(Self::from_predicate))
            .unwrap_or_else(|_| Symbol::from(s).into()))
    }
}

impl<L, Q, P> InnerLang for Symbols<L, Q, P>
where
    L: InnerLang,
    Q: InnerLang,
    P: InnerLang,
{
    fn arity(&self) -> Option<usize> {
        match_as_trait!(self => {
          Self::BaseTA(x) | Self::Predicate(x) => {x.arity()},
          Self::Quant(q) => {q.arity().map(|x| x+1)},
          _ => {None}
        })
    }
}

impl<U> FromOp for Lang<U>
where
    U: InnerLang,
    anyhow::Error: std::convert::From<<U as std::str::FromStr>::Err>,
{
    type Error = anyhow::Error;

    fn from_op(op: &str, args: Vec<egg::Id>) -> Result<Self, Self::Error> {
        let s = Self {
            symb: op.parse()?,
            args,
        };
        match s.symb.arity() {
            Some(a) if a != s.arity() => Err(anyhow!(
                "wrong number of arguments (got {:} expected {a:})",
                s.arity()
            )),
            _ => Ok(s),
        }
    }
}

impl InnerLang for Symbol {
    fn arity(&self) -> Option<usize> {
        None
    }
}

impl FromStr for Var {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.chars();
        if '!' == iter.next().ok_or(anyhow!("var cannot be empty"))? {
            Ok(Var(iter.as_str().parse()?))
        } else {
            Err(anyhow!("var must start by '!'"))
        }
    }
}

impl<L, Q, P> From<Var> for Symbols<L, Q, P> {
    fn from(Var(i): Var) -> Self {
        Self::Var(i)
    }
}

impl<L, Q, P> From<Symbol> for Symbols<L, Q, P> {
    fn from(v: Symbol) -> Self {
        Self::Other(v)
    }
}

static FRESH_VARS_COUNT: AtomicU32 = AtomicU32::new(u32::MAX / 4);

macro_rules! declare_lang {
    ($t:ident; { $($n:ident/$a:literal)* }) => {
      #[derive(Debug, Ord, PartialOrd, PartialEq, Eq, Hash, Copy, Clone)]
      pub enum $t {
        $($n),*
      }

      impl ::core::str::FromStr for $t {
        type Err = ::anyhow::Error;

        fn from_str(s:&str) -> ::anyhow::Result<Self> {
          match s {
            $(::std::stringify!($n) => Ok(Self::$n),)*
            _ => Err(::anyhow::anyhow!("unknown symbol: {s}"))
          }
        }
      }

      impl $crate::language::InnerLang for $t {
        fn arity(&self) -> Option<usize>{
          match self {
            $(Self::$n => Some($a)),*
          }
        }
      }
    };
    ($t:ident; { $($n:ident/$a:literal),* }) => {
      declare_lang!($t; { $($n/$a)* });
    }
}

#[cfg(test)]
mod test {
  declare_lang!(Test; {
    A/1, B/2, C/3
  });
}