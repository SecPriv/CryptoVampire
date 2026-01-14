use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Deref;

use cryptovampire_smt::SmtHead;
use egg::{Id, Language, PatternAst, RecExpr};
use serde::Serialize;
use steel::SteelErr;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;
use utils::{ereturn_if, implvec, match_eq};

use crate::input::Registerable;
use crate::input::shared_cryptography::ShrCrypto;
use crate::protocol::MacroKind;
use crate::terms::{
    Alias, AliasRewrite, BUILTINS, EXISTS, Exists, FIND_SUCH_THAT, FOBinder, Formula,
    FunctionCollection, FunctionFlags, LAMBDA_O, LAMBDA_S, MACRO_COND, MACRO_EXEC, MACRO_FRAME,
    MACRO_INPUT, MACRO_MSG, NOT, Quantifier, QuantifierIndex, QuantifierT, Signature, Sort,
    UNFOLD_COND, UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG, Variable, builtin,
};
use crate::utils::{InnerSmartCow, LightClone, SmartCow};
use crate::{Lang, LangVar, fresh};

/// Helper macro to generate `is_*` methods for `Function` based on `FunctionFlags`.
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

/// The inner representation of a function, containing all its properties.
#[non_exhaustive]
#[derive(Debug, Clone, Serialize)]
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
    /// Creates a new `InnerFunction` with the given name and signature, and default flags.
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

impl Ord for InnerFunction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}
impl PartialOrd for InnerFunction {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for InnerFunction {}

impl PartialEq for InnerFunction {
    fn eq(&self, _: &Self) -> bool {
        unimplemented!("you should use equality on `Function`")
    }
}

impl Hash for InnerFunction {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {
        unimplemented!("you should use the Hash on `Function`")
    }
}

// TODO: make comparison faster
/// Main type for function in this crate
///
/// This is basicaly a somewhat smart pointer to an [InnerFunction].
#[derive(Clone, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash, Steel)]
#[steel(equality)]
pub struct Function(SmartCow<InnerFunction>);

impl Function {
    /// Build a [Function] from an inner reference.
    ///
    /// Mostly useful for the constants because this is `const`
    pub const fn from_ref(content: &'static InnerSmartCow<InnerFunction>) -> Self {
        Self(SmartCow::from_static(content))
    }

    /// Creates a new `Function` from an `InnerFunction`.
    pub fn new(content: InnerFunction) -> Self {
        Self(SmartCow::new(content))
    }

    /// The arity of the function
    ///
    /// [egg::RecExpr] are check at build time, so that all functions have the right arity
    pub fn arity(&self) -> usize {
        self.signature.arity()
    }

    #[inline]
    pub fn args_sorts(&self) -> impl Iterator<Item = Sort> {
        self.signature.inputs.iter().copied()
    }

    pub fn args_vars(&self) -> impl Iterator<Item = Variable> {
        self.args_sorts().map(|s| fresh!(s))
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
    pub const fn const_clone(&self) -> Self {
        Self(self.0.const_clone())
    }

    /// Returns the `QuantifierIndex` if this function is a quantifier, otherwise `None`.
    pub fn get_quantifier_index(&self) -> Option<QuantifierIndex> {
        self.has_quantifier_idx().then_some(QuantifierIndex {
            temporary: self.is_temporary(),
            index: self.quantifier_idx,
        })
    }

    /// Retrieves the `Quantifier` associated with this function from the `FunctionCollection`.
    pub fn get_quantifier<'a>(&self, functions: &'a FunctionCollection) -> Option<&'a Quantifier> {
        self.get_quantifier_index()?.get(functions)
    }

    /// Retrieves the `Exists` quantifier associated with this function, if it is one.
    pub fn get_exists<'a>(&self, functions: &'a FunctionCollection) -> Option<&'a Exists> {
        Exists::try_from_ref(self.get_quantifier(functions)?)
    }

    /// Returns the protocol index if this function represents a protocol, otherwise `None`.
    pub fn get_protocol_index(&self) -> Option<usize> {
        self.is_protocol().then_some(self.protocol_idx)
    }

    /// Returns the step index if this function represents a protocol step, otherwise `None`.
    pub fn get_step_index(&self) -> Option<usize> {
        self.is_step().then_some(self.step_idx)
    }

    /// Returns a reference to the `Alias` if this function has one, otherwise `None`.
    pub fn get_alias(&self) -> Option<&Alias> {
        self.alias.as_ref()
    }

    /// Converts the function into its corresponding `SmtHead` representation, if it has one.
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

    /// Applies the function to a list of `RecFOFormula` arguments, returning a new `RecFOFormula`.
    pub fn rapp(&self, args: implvec!(Formula)) -> Formula {
        Formula::app(self.clone(), args.into_iter().collect())
    }

    /// Builds a [SimplLang]. Panics if not valid
    /// Applies the function to a list of `egg::Id` arguments, returning a `Lang` node.
    ///
    /// # Panics
    ///
    /// Panics if the number of arguments does not match the function's arity.
    pub fn app_id(&self, ids: implvec!(Id)) -> Lang {
        Lang::new(self.clone(), ids)
    }

    /// Applies the function to a slice of `Lang` expressions, returning a `RecExpr<Lang>`.
    pub fn app<E: AsRef<[Lang]>>(&self, ids: &[E]) -> RecExpr<Lang> {
        let head = self.app_id((0..ids.len()).map(Id::from));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }

    /// Applies the function to a slice of `LangVar` expressions, returning a `PatternAst<Lang>`.
    pub fn app_var<E: AsRef<[LangVar]>>(&self, ids: &[E]) -> PatternAst<Lang> {
        let head = egg::ENodeOrVar::ENode(self.app_id((0..ids.len()).map(Id::from)));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }

    /// Applies the function with no arguments, returning a `RecExpr<Lang>`.
    pub fn app_empty(&self) -> RecExpr<Lang> {
        self.app::<[_; 0]>(&[])
    }

    /// Applies the function with no arguments, returning a `PatternAst<Lang>`.
    pub fn app_empty_var(&self) -> PatternAst<Lang> {
        self.app_var::<[_; 0]>(&[])
    }

    /// Converts the function into an `FOBinder` if it represents a known binder.
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

    /// Returns `true` if the function is statically allocated (i.e., borrowed), `false` otherwise.
    pub const fn is_static(&self) -> bool {
        self.0.is_static()
    }

    /// Returns `true` if the function is a special subterm that requires custom handling.
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

    /// Returns `true` if the function is a special deduction rule.
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

    /// Returns `true` if the function represents a protocol.
    #[inline]
    pub fn is_protocol(&self) -> bool {
        ereturn_if!(!self.flags.contains(FunctionFlags::PROTOCOL), false);
        // will return true
        assert_eq!(self.signature.output, Sort::Protocol);
        true
    }

    /// Returns `true` if the function is an alias.
    #[inline]
    pub fn is_alias(&self) -> bool {
        self.get_alias().is_some()
    }

    /// Returns `true` if the function represents a protocol step.
    #[inline]
    pub fn is_step(&self) -> bool {
        ereturn_if!(!self.flags.contains(FunctionFlags::STEP), false);
        // will return true
        assert_eq!(self.signature.output, Sort::Time);
        true
    }

    /// Returns `true` if the function represents a datatype (nonce or protocol).
    pub fn is_datatype(&self) -> bool {
        self.is_nonce() || self.is_protocol()
    }

    is_fun!(is_debruijn; LAMBDA; "related to De Bruijn variables");
    is_fun!(is_prolog_only; PROLOG_ONLY;
            "This function should appear outside of prolog (e.g., doesn't make sense in smt)");
    is_fun!(is_if_then_else; IF_THEN_ELSE;
            "Returns `true` if the function is an if-then-else construct.");
    is_fun!(is_out_of_term_algebra; SMT_ONLY| PROLOG_ONLY;
            "Returns `true` if the function is outside the term algebra (e.g., SMT-only or Prolog-only).");
    is_fun!(is_nonce; NONCE;
            "Returns `true` if the function represents a nonce.");
    is_fun!(is_quantifier; FIND_SUCH_THAT| BINDER;
            "Returns `true` if the function is a quantifier (e.g., `EXISTS`, `FIND_SUCH_THAT`).");
    is_fun!(has_quantifier_idx; BINDER | FIND_SUCH_THAT | SKOLEM | QUANTIFIER_FRESH;
            "Returns `true` if the function has an associated quantifier index.");
    is_fun!(is_egg_binder; BINDER;
            "Returns `true` if the function is an `egg` binder.");
    is_fun!(is_temporary; TEMPORARY;
            "Returns `true` if the function is temporary.");
    is_fun!(is_fresh; FRESH;
            "Returns `true` if the function represents something fresh.");
    #[inline]
    /// Returns `true` if the function is a publications step.
    pub fn is_publish_step(&self) -> bool {
        static FLAGS: FunctionFlags = const_fun_flags!(PUBLICATION_STEP | STEP);
        self.flags.contains(FLAGS)
    }
    is_fun!(is_should_not_declare_in_smt; PROLOG_ONLY | BUILTIN_SMT;
r" Should not appear in an smt file

Because smt has a syntax for it, or it's a prolog trick, or ...");

    is_fun!(is_builtin_smt; BUILTIN_SMT; "The function already has an equivalent in smt");

    #[allow(non_snake_case)]
    pub fn is_part_of_F(&self) -> bool {
        self.flags
            .difference(const_fun_flags!(
                BUILTIN | BUILTIN_SMT | TEMPORARY | IF_THEN_ELSE | BINDER | CUSTOM_DEDUCE
            ))
            .is_empty()
    }

    /// means that you can fearlessly subtitute in it
    pub fn is_ok_for_substitution(&self) -> bool {
        (!self
            .flags
            .intersects(FunctionFlags::PROLOG_ONLY | FunctionFlags::SMT_ONLY))
            || self
                .flags
                .contains(FunctionFlags::LIST_CONSTR | FunctionFlags::LIST_FA_CONSTR)
            || (self == &LAMBDA_O)
            || (self == &LAMBDA_S)
            || (self == &EXISTS)
            || (self == &FIND_SUCH_THAT)
    }

    // =========================================================
    // ====================== Steel API ========================
    // =========================================================

    /// Creates a new `Function` instance for use with the Steel VM.
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

    /// Creates a new `Function` instance representing a nonce for use with the Steel VM.
    pub fn steel_new_nonce(name: String, signature: Signature) -> Self {
        assert_eq!(signature.output, Sort::Nonce);
        Self::new(InnerFunction {
            flags: FunctionFlags::NONCE,
            ..InnerFunction::new(name.into(), signature)
        })
    }

    /// Creates a new `Function` instance representing an alias for use with the Steel VM.
    pub fn steel_new_alias(
        name: String,
        signature: Signature,
        alias: Alias,
    ) -> Result<Self, SteelErr> {
        // cheks the alias is well formed
        for AliasRewrite { from, .. } in alias.iter() {
            if from.len() != signature.arity() {
                let err = SteelErr::new(
                    steel::rerrs::ErrorKind::ArityMismatch,
                    format!(
                        "expected the arity of each branch to match the function (got {} expected \
                         {})",
                        from.len(),
                        signature.arity()
                    ),
                );
                return Err(err);
            }
        }

        Ok(Self::new(InnerFunction {
            alias: Some(alias),
            ..InnerFunction::new(name.into(), signature)
        }))
    }

    /// Returns the name of the function as a `String` for use with the Steel VM.
    pub fn steel_name(&self) -> String {
        self.name.clone().into_owned()
    }
}

pub(crate) static SCHEME_PREFIX: &str = "__pre_";
impl Registerable for Function {
    /// Registers the `Function` type and its associated methods with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module);
        module
            .register_type::<Self>("Function?")
            .register_fn("mk-fun", Self::steel_new)
            .register_fn("mk-nonce", Self::steel_new_nonce)
            .register_fn("mk-alias", Self::steel_new_alias)
            .register_fn("arity", Self::arity)
            .register_fn("function-name", Self::steel_name);

        for fun in BUILTINS {
            module.register_value(
                &format!("{SCHEME_PREFIX}{}", fun.name),
                fun.clone().into_steelval().unwrap(),
            );
        }

        module
    }
}

impl Display for Function {
    /// Formats the function for display, showing its name.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.name.as_ref(), f)
    }
}

impl Debug for Function {
    /// Formats the function for debugging, showing its name.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // f.debug_tuple("Function").field(&self.0).finish()
        Display::fmt(&self, f)
    }
}

impl Deref for Function {
    /// Dereferences to the inner `InnerFunction`.
    type Target = InnerFunction;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl AsRef<Self> for Function {
    /// Returns a reference to `self`.
    fn as_ref(&self) -> &Self {
        self
    }
}

impl LightClone for Function {}
