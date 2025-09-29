use std::borrow::Cow;
use std::fmt::Display;
use std::ops::Deref;

use cryptovampire_smt::SmtHead;
use egg::{Id, Language, PatternAst, RecExpr};
use serde::Serialize;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;
use utils::quack::CowArc;
use utils::{ereturn_if, implvec, match_eq};

use crate::input::Registerable;
use crate::input::shared_cryptography::ShrCrypto;
use crate::protocol::{MacroKind};
use crate::terms::{
    builtin, Alias, Exists, FOBinder, FunctionCollection, FunctionFlags, Quantifier, QuantifierIndex, QuantifierT, RecFOFormula, Signature, Sort, BUILTINS, EXISTS, HAPPENS, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, NOT, TRUE, UNFOLD_COND, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG,  FIND_SUCH_THAT
};
use crate::utils::LightClone;
use crate::{Lang, LangVar};

macro_rules! is_fun {
    ($name:ident; $($flag:ident)|+) => {
        #[inline]
        pub fn $name(&self) -> bool {
            static FLAGS: FunctionFlags =
                const_fun_flags!($($flag)|+);

            self.flags.intersects(FLAGS)
        }
    };
    ($name:ident; $($flag:ident)|+; $t:literal) => {
        #[inline] #[doc = $t]
        pub fn $name(&self) -> bool {
            static FLAGS: FunctionFlags =
                const_fun_flags!($($flag)|+);

            self.flags.intersects(FLAGS)
        }
    };
}

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct InnerFunction {
    pub name: Cow<'static, str>,
    pub signature: Signature,
    pub alias: Option<Alias>,
    pub flags: FunctionFlags,
    pub quantifier_idx: usize,
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
            quantifier_idx: 0,
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

    pub fn get_quantifier_index(&self) -> Option<QuantifierIndex> {
        self.has_quantifier_idx().then_some(
            QuantifierIndex {
                temporary: self.is_temporary(),
                index: self.quantifier_idx,
            }
        )
    }

    pub fn get_quantifier<'a>(&self, functions: &'a FunctionCollection) -> Option<&'a Quantifier> {
        self.get_quantifier_index()?.get(functions)
    }

    pub fn get_exists<'a>(&self, functions: &'a FunctionCollection) -> Option<&'a Exists> {
        Exists::try_from_ref(self.get_quantifier(functions)?)
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

    // =========================================================
    // ========================= app ===========================
    // =========================================================

    pub fn rapp(&self, args: implvec!(RecFOFormula)) -> RecFOFormula {
        RecFOFormula::app(self.clone(), args.into_iter().collect())
    }

    /// Builds a [SimplLang]. Panics if not valid
    pub fn app_id(&self, ids: implvec!(Id)) -> Lang {
        Lang::new(self.clone(), ids)
    }

    pub fn app<E: AsRef<[Lang]>>(
        &self,
        ids: &[E],
    ) -> RecExpr<Lang> {
        let head = self.app_id((0..ids.len()).map(Id::from));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }

    pub fn app_var<E: AsRef<[LangVar]>>(&self, ids: &[E]) -> PatternAst<Lang> {
        let head = egg::ENodeOrVar::ENode(self.app_id((0..ids.len()).map(Id::from)));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }

    pub fn app_empty(&self) -> RecExpr<Lang> {
        self.app::<[_; 0]>(&[])
    }

    pub fn app_empty_var(&self) -> PatternAst<Lang> {
        self.app_var::<[_; 0]>(&[])
    }

    pub fn as_fobinder(&self) -> Option<FOBinder> {
        match_eq!(self => {
            EXISTS => { Some(FOBinder::Exists) },
            FIND_SUCH_THAT => {Some(FOBinder::FindSuchThat)},
            _ => { None }
        })
    }

    // =========================================================
    // ==================== is functions =======================
    // =========================================================
    #[inline]
    pub fn is_special_subterm(&self) -> bool {
        static SPECIAL_SUBTERM: FunctionFlags = const_fun_flags!(
            PROLOG_ONLY
                | MACRO
                | UNFOLD
                | CUSTOM_SUBTERM
                | BINDER
                | FIND_SUCH_THAT
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
                | BINDER
                | FIND_SUCH_THAT
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

    pub fn is_datatype(&self) -> bool {
        self.is_nonce() || self.is_protocol()
    }

    is_fun!(is_prolog_only; PROLOG_ONLY; 
            "This function should appear outside of prolog (e.g., doesn't make sense in smt)");
    is_fun!(is_if_then_else; IF_THEN_ELSE);
    is_fun!(is_out_of_term_algebra; SMT_ONLY| PROLOG_ONLY);
    is_fun!(is_nonce; NONCE);
    is_fun!(is_quantifier; FIND_SUCH_THAT| BINDER);
    is_fun!(has_quantifier_idx; BINDER | FIND_SUCH_THAT | SKOLEM | QUANTIFIER_FRESH);
    is_fun!(is_egg_binder; BINDER);
    is_fun!(is_temporary; TEMPORARY);
    is_fun!(is_should_not_declare_in_smt; PROLOG_ONLY | BUILTIN_SMT;
r" Should not appear in an smt file

Because smt has a syntax for it, or it's a prolog trick, or ...");

    is_fun!(is_builtin_smt; BUILTIN_SMT; "The function already has an equivalent in smt");

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

impl LightClone for Function {}