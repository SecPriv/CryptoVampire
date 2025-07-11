use std::borrow::Cow;
use std::fmt::Display;
use std::ops::Deref;

use cryptovampire_smt::SmtHead;
use logic_formula::egg::{SimplLang, SimpleDiscriminant};
use serde::Serialize;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;
use utils::quack::CowArc;
use utils::{ereturn_if, implvec, match_eq};

use crate::input::Registerable;
use crate::input::shared_cryptography::ShrCrypto;
use crate::protocol::{MacroKind, ProtocolLanguage};
use crate::terms::{
    Alias, BUILTINS, Exists, FunctionCollection, FunctionFlags, HAPPENS, MACRO_COND, MACRO_EXEC,
    MACRO_FRAME, MACRO_INPUT, MACRO_MSG, NOT, RecFOFormula, Signature, Sort, TRUE, UNFOLD_COND,
    UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG, builtin,
};

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct InnerFunction {
    pub name: Cow<'static, str>,
    pub signature: Signature,
    pub alias: Option<Alias>,
    pub flags: FunctionFlags,
    pub exists_idx: usize,
    pub protocol_idx: usize,
    pub step_idx: usize,
    pub cryptography: cow![usize],
}

impl InnerFunction {
    pub const fn new(name: Cow<'static, str>, signature: Signature) -> Self {
        Self {
            name,
            signature,
            alias: None,
            flags: FunctionFlags::empty(),
            exists_idx: 0,
            protocol_idx: 0,
            step_idx: 0,
            cryptography: Cow::Borrowed(&[]),
        }
    }
}

// TODO: make comparison faster
/// Main type for function in this crate
///
/// This is basicaly a somewhat smart pointer to an [InnerFunction].
#[derive(Debug, Clone, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash, Steel)]
pub struct Function(CowArc<'static, InnerFunction>);

impl Function {
    /// Build a [Function] from an inner reference.
    ///
    /// Mostly useful for the constants because this is `const`
    pub const fn from_ref(content: &'static InnerFunction) -> Self {
        Self(CowArc::from_ref(content))
    }

    pub fn new(inner: InnerFunction) -> Self {
        Self(CowArc::from(inner))
    }

    /// The arity of the function
    ///
    /// [egg::RecExpr] are check at build time, so that all functions have the right arity
    pub fn arity(&self) -> usize {
        self.signature.arity()
    }

    /// Get the `macro` function from a [MacroKind]
    pub const fn macro_from_kind(kind: MacroKind) -> &'static Self {
        match kind {
            MacroKind::Frame => &MACRO_FRAME,
            MacroKind::Input => &MACRO_INPUT,
            MacroKind::Cond => &MACRO_COND,
            MacroKind::Msg => &MACRO_MSG,
            MacroKind::Exec => &MACRO_EXEC,
        }
    }

    /// Get the `unfold` function from a [MacroKind]
    pub const fn unfold_from_kind(kind: MacroKind) -> &'static Self {
        match kind {
            MacroKind::Frame => &UNFOLD_FRAME,
            MacroKind::Input => &UNFOLD_INPUT,
            MacroKind::Cond => &UNFOLD_COND,
            MacroKind::Msg => &UNFOLD_MSG,
            MacroKind::Exec => &UNFOLD_EXEC,
        }
    }

    /// static [Function] can be statically cloned. This function lets you do
    /// that. It returns [None] when the [Function] is not static
    pub const fn const_clone(&self) -> Option<Self> {
        match self.0 {
            CowArc::Owned(_) => None,
            CowArc::Borrowed(x) => Some(Self::from_ref(x)),
        }
    }

    pub fn get_exist_index(&self) -> Option<usize> {
        self.flags
            .intersects(const_fun_flags!(EXISTS | SKOLEM | EXISTS_FRESH))
            .then_some(self.exists_idx)
    }

    pub fn get_exists<'a>(&self, function: &'a FunctionCollection) -> Option<&'a Exists> {
        let idx = self.get_exist_index()?;
        function.quantifiers().get(idx)
    }

    pub fn get_protocol_index(&self) -> Option<usize> {
        self.is_protocol().then_some(self.protocol_idx)
    }

    pub fn get_step_index(&self) -> Option<usize> {
        self.is_step().then_some(self.step_idx)
    }

    pub fn get_alias(&self) -> Option<&Alias> {
        self.alias.as_ref()
    }

    pub fn as_smt_head(&self) -> Option<SmtHead> {
        use SmtHead::*;
        use builtin::*;
        match_eq! { self => {
            AND => { Some(And) },
            NOT => { Some(Not) },
            OR => { Some(Or) },
            IMPLIES => { Some(Implies) },
            EQ => { Some(Eq) },
            BITE | MITE => {Some(If)},
            TRUE => { Some(True) },
            FALSE => { Some(False) },
            _ => { None }
        }}
    }

    pub fn rapp(&self, args: implvec!(RecFOFormula)) -> RecFOFormula {
        RecFOFormula::app(self.clone(), args.into_iter().collect())
    }

    // =========================================================
    // ==================== is functions =======================
    // =========================================================

    /// Should not appear in an smt file
    ///
    /// Because smt has a syntax for it, or it's a prolog trick, or ...
    #[inline]
    pub fn is_should_not_declare_in_smt(&self) -> bool {
        static SHOULD_NOT_DECLARE_IN_SMT: FunctionFlags =
            const_fun_flags!(PROLOG_ONLY | BUILTIN_SMT);

        self.flags.intersects(SHOULD_NOT_DECLARE_IN_SMT)
    }

    /// The function already has an equivalent in smt
    #[inline]
    pub fn is_builtin_smt(&self) -> bool {
        self.flags.intersects(FunctionFlags::BUILTIN_SMT)
    }

    #[inline]
    pub fn is_special_subterm(&self) -> bool {
        static SPECIAL_SUBTERM: FunctionFlags = const_fun_flags!(
            PROLOG_ONLY
                | MACRO
                | UNFOLD
                | CUSTOM_SUBTERM
                | EXISTS
                | SKOLEM
                | SMT_ONLY
                | IF_THEN_ELSE
        );

        self != &NOT
            && (self.flags.intersects(SPECIAL_SUBTERM) || self.is_protocol() || self.is_alias())
    }

    #[inline]
    pub fn is_special_deduce(&self) -> bool {
        static SPECIAL_DEDUCE: FunctionFlags = const_fun_flags!(
            PROLOG_ONLY
                | MACRO
                | UNFOLD
                | CUSTOM_DEDUCE
                | EXISTS
                | SKOLEM
                | NONCE
                | SMT_ONLY
                | IF_THEN_ELSE
        );
        self.flags.intersects(SPECIAL_DEDUCE) || self.is_alias()
    }

    #[inline]
    pub fn is_protocol(&self) -> bool {
        ereturn_if!(!self.flags.contains(FunctionFlags::PROTOCOL), false);
        // will return true
        assert_eq!(self.signature.output, Sort::Protocol);
        true
    }

    #[inline]
    pub fn is_alias(&self) -> bool {
        self.get_alias().is_some()
    }

    #[inline]
    pub fn is_step(&self) -> bool {
        ereturn_if!(!self.flags.contains(FunctionFlags::STEP), false);
        // will return true
        assert_eq!(self.signature.output, Sort::Time);
        true
    }

    /// This function should appear outside of prolog (e.g., doesn't make sense in smt)
    #[inline]
    pub fn is_prolog_only(&self) -> bool {
        self.flags.intersects(FunctionFlags::PROLOG_ONLY)
    }

    #[inline]
    pub fn is_if_then_else(&self) -> bool {
        self.flags.intersects(FunctionFlags::IF_THEN_ELSE)
    }

    #[inline]
    pub fn is_out_of_term_algebra(&self) -> bool {
        self.flags
            .intersects(FunctionFlags::SMT_ONLY | FunctionFlags::PROLOG_ONLY)
    }

    // =========================================================
    // ====================== Steel API ========================
    // =========================================================

    pub fn steel_new(name: String, signature: Signature, crypto: Vec<ShrCrypto>) -> Self {
        let cryptography = crypto
            .iter()
            .map(|ShrCrypto { index, .. }| *index)
            .collect();
        Self::new(InnerFunction {
            cryptography,
            ..InnerFunction::new(name.into(), signature)
        })
    }

    pub fn steel_new_nonce(name: String, signature: Signature) -> Self {
        assert_eq!(signature.output, Sort::Nonce);
        Self::new(InnerFunction {
            flags: FunctionFlags::NONCE,
            ..InnerFunction::new(name.into(), signature)
        })
    }

    pub fn steel_new_alias(name: String, signature: Signature, alias: Alias) -> Self {
        Self::new(InnerFunction {
            alias: Some(alias),
            ..InnerFunction::new(name.into(), signature)
        })
    }
}

impl Registerable for Function {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module);
        module
            .register_type::<Function>("Function?")
            .register_fn("fun", Self::steel_new)
            .register_fn("mk-nonce", Self::steel_new_nonce)
            .register_fn("mk-alias", Self::steel_new_alias);

        for fun in BUILTINS {
            module.register_value(&fun.name, fun.clone().into_steelval().unwrap());
        }

        module
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}

impl Deref for Function {
    type Target = InnerFunction;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Self> for Function {
    fn as_ref(&self) -> &Self {
        self
    }
}

// impl Eq for Function {}

// impl PartialEq for Function {
//     fn eq(&self, other: &Self) -> bool {
//         match (&self.0, &other.0) {
//             (CowArc::Owned(a), CowArc::Owned(b)) => Arc::ptr_eq(a, b),
//             (CowArc::Borrowed(a), CowArc::Borrowed(b)) => ::core::ptr::eq(a, b),
//             _ => false,
//         }
//     }
// }

// impl PartialOrd for Function {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         if self == other {
//             // equality if defined by pointer
//             Some(Ordering::Equal)
//         } else {
//             // order by the content
//             match InnerFunction::cmp(self, other) {
//                 Ordering::Equal => None,
//                 x => Some(x),
//             }
//         }
//     }
// }

// impl Ord for Function {
//     fn cmp(&self, other: &Self) -> Ordering {
//         Self::partial_cmp(self, other).expect(
//             "duplicate function at two different location in memory! (The \
//             comparison algorithm is unsound in those cases, please avoid \
//             declaring function twice)",
//         )
//     }
// }

// impl Hash for Function {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         match &self.0 {
//             CowArc::Owned(x) => Arc::as_ptr(x),
//             CowArc::Borrowed(x) => *x as *const _,
//         }
//         .hash(state);
//     }
// }

// ~~~~~~~~~~~~ egg::Language ~~~~~~~~~~~~~~~

impl SimpleDiscriminant for Function {
    fn valid(&self, ids: &[egg::Id]) -> bool {
        self.arity() == ids.len()
    }
}

impl<const N: usize> ProtocolLanguage for SimplLang<Function, N> {
    fn mk_happens(step: egg::Id) -> Self {
        HAPPENS.app_id([step])
    }

    fn mk_true() -> Self {
        TRUE.app_id([])
    }

    fn mk_macro(kind: MacroKind, step: egg::Id, ptcl: egg::Id) -> Self {
        Function::macro_from_kind(kind).app_id([step, ptcl])
    }

    fn mk_unfold(kind: MacroKind, step: egg::Id, ptcl: egg::Id) -> Self {
        Function::unfold_from_kind(kind).app_id([step, ptcl])
    }
}
