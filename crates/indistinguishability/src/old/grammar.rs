use std::convert::identity;

use egg::Language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Grammar<U, S = egg::Symbol> {
    Const(S),
    Nonce(U),
    Enc {
        m: U,
        r: U,
        k: U,
    },
    Dec {
        c: U,
        k: U,
    },
    Pk(U),
    Ite {
        cond: U,
        left: U,
        right: U,
    },
    Tuple(U, U),
    P1(U),
    P2(U),
    Eq(U, U),
    Length(U),
    Zeroes(U),
    #[default]
    True,
    False,
    Eta,
    Input(U),
    Equiv(U),
}

mod consts {
    pub const fn CONST<S>(s: S) -> Grammar<(), S> {
        Grammar::Const(s)
    }
    pub const fn NONCE<S>() -> Grammar<(), S> {
        Grammar::Nonce(())
    }
    pub const fn ENC<S>() -> Grammar<(), S> {
        Grammar::Enc {
            m: (),
            r: (),
            k: (),
        }
    }
    pub const fn DEC<S>() -> Grammar<(), S> {
        Grammar::Dec { c: (), k: () }
    }
    pub const fn PK<S>() -> Grammar<(), S> {
        Grammar::Pk(())
    }
    pub const fn ITE<S>() -> Grammar<(), S> {
        Grammar::Ite {
            cond: (),
            left: (),
            right: (),
        }
    }
    pub const fn TUPLE<S>() -> Grammar<(), S> {
        Grammar::Tuple((), ())
    }
    pub const fn P1<S>() -> Grammar<(), S> {
        Grammar::P1(())
    }
    pub const fn P2<S>() -> Grammar<(), S> {
        Grammar::P2(())
    }
    pub const fn EQ<S>() -> Grammar<(), S> {
        Grammar::Eq((), ())
    }
    pub const fn LENGTH<S>() -> Grammar<(), S> {
        Grammar::Length(())
    }
    pub const fn ZEROES<S>() -> Grammar<(), S> {
        Grammar::Zeroes(())
    }
    pub const fn TRUE<S>() -> Grammar<(), S> {
        Grammar::True
    }
    pub const fn FALSE<S>() -> Grammar<(), S> {
        Grammar::False
    }
    pub const fn ETA<S>() -> Grammar<(), S> {
        Grammar::Eta
    }
    pub const fn INPUT<S>() -> Grammar<(), S> {
        Grammar::Input(())
    }
    pub const fn EQUIV<S>() -> Grammar<(), S> {
        Grammar::Equiv(())
    }
}
pub use consts::*;
use smallvec::{smallvec_inline, SmallVec};

pub struct AsApp<U, S = egg::Symbol> {
    head: Grammar<(), S>,
    args: smallvec::SmallVec<[U; 3]>,
}

impl<U, S> AsApp<U, S> {
    pub const fn new(head: Grammar<(), S>, args: smallvec::SmallVec<[U; 3]>) -> Self {
        Self { head, args }
    }
}

impl<U, S> Grammar<U, S> {
    pub fn map2<F, G, V, T>(self, mut f: &mut F, g: G) -> Grammar<V, T>
    where
        F: FnMut(U) -> V,
        G: FnOnce(S) -> T,
    {
        use Grammar::*;
        match self {
            Const(s) => Const(g(s)),
            Nonce(u) => Nonce(f(u)),
            Enc { m, r, k } => Enc {
                m: f(m),
                r: f(r),
                k: f(k),
            },
            Dec { c, k } => Dec { c: f(c), k: f(k) },
            Pk(u) => Pk(f(u)),
            Ite { cond, left, right } => Ite {
                cond: f(cond),
                left: f(left),
                right: f(right),
            },
            Tuple(l, r) => Tuple(f(l), f(r)),
            P1(u) => P1(f(u)),
            P2(u) => P2(f(u)),
            Eq(l, r) => Eq(f(l), f(r)),
            Length(u) => Length(f(u)),
            Zeroes(u) => Zeroes(f(u)),
            True => True,
            False => False,
            Eta => Eta,
            Input(u) => Input(f(u)),
            Equiv(u) => Equiv(f(u)),
        }
    }

    pub fn map<F, V>(self, mut f: impl FnMut(U) -> V) -> Grammar<V, S> {
        self.map2(&mut f, identity)
    }

    pub const fn into_app(self) -> AsApp<U, S> {
        use Grammar::*;
        match self {
            Const(s) => AsApp::new(Const(s), SmallVec::new_const()),
            Nonce(u) => AsApp::new(Nonce(()), smallvec_inline![u]),
            Enc { m, r, k } => todo!(),
            Dec { c, k } => todo!(),
            Pk(_) => todo!(),
            Ite { cond, left, right } => todo!(),
            Tuple(_, _) => todo!(),
            P1(_) => todo!(),
            P2(_) => todo!(),
            Eq(_, _) => todo!(),
            Length(_) => todo!(),
            Zeroes(_) => todo!(),
            True => todo!(),
            False => todo!(),
            Eta => todo!(),
            Input(_) => todo!(),
            Equiv(_) => todo!(),
        }
    }
}

impl Language for Grammar<egg::Id> {
    fn matches(&self, other: &Self) -> bool {
        todo!()
    }

    fn children(&self) -> &[egg::Id] {
        todo!()
    }

    fn children_mut(&mut self) -> &mut [egg::Id] {
        todo!()
    }
}
