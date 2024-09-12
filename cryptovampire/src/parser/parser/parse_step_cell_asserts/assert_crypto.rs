use anyhow::Context;

use crate::{
    bail_at,
    parser::{
        ast::{self, Options},
        error::WithLocation,
        parser::Environement,
        Location, MResult, Pstr,
    },
};
use cryptovampire_lib::{
    environement::traits::Realm,
    formula::function::signature::Signature,
    problem::crypto_assumptions::{
        CryptoAssumption, CryptoFlag, EufCma, IntCtxt, Nonce, UfCmaBuilder, Unfolding,
        EUF_CMA_PK_SIGNATURE, EUF_CMA_SIGN_SIGNATURE, EUF_CMA_VERIFY_SIGNATURE,
        INT_CTXT_DEC_SIGNATURE, INT_CTXT_ENC_SIGNATURE, INT_CTXT_FAIL_SIGNATURE,
        UF_CMA_MAC_SIGNATURE, UF_CMA_VERIFY_SIGNATURE,
    },
};
use utils::{destvec, implvec, string_ref::StrRef, traits::NicerError};

pub fn parse_asserts_crypto<'a, 'str, 'bump, S>(
    env: &'a Environement<'bump, 'str, S>,
    crypto: implvec!(&'a ast::AssertCrypto<'str, S>),
) -> MResult<Vec<CryptoAssumption<'bump>>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    crypto
        .into_iter()
        .map(|ac| parse_assert_crypto(env, ac))
        .collect()
}

pub fn parse_assert_crypto<'str, 'bump, S>(
    env: &Environement<'bump, 'str, S>,
    crypto: &ast::AssertCrypto<'str, S>,
) -> MResult<CryptoAssumption<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let ast::AssertCrypto {
        span,
        name,
        functions,
        options,
    } = crypto;

    match name.content.borrow() {
        "nonce" => Ok(CryptoAssumption::Nonce(Nonce)),
        "memory_cell" => Ok(CryptoAssumption::MemoryCell(Default::default())),
        "euf-cma" | "euf_cma" => parse_euf_cma(env, functions, options, *span),
        "uf-cma" | "uf_cma" => parse_uf_cma(env, functions, options, *span),
        "int-ctxt" | "int_ctxt" => parse_int_ctxt(env, functions, *span),
        "unfolding" => parse_unfolding(env, functions, options, *span),
        n => name
            .span
            .bail_with(|| format!("unknown crypto assertion: {n}")),
    }
    .debug_continue()
}

macro_rules! verify_sign {
    ($env:ident; $ast:ident, $fun:ident, $signature:ident, $arity:literal) => {
        let $fun = *$env.find_function($ast.span(), $ast.name().borrow()).and_then(|f| {
            f.as_function()
                .with_context(|| format!("{} should be a function", $ast.name()))
                .with_location($ast.span())
            // .ok_or_else(|| merr($ast.span(), format!("{} should be a function", $ast.name())))
        })?;
        $signature
            .as_ref()
            .unify(&$fun.signature(), &Realm::Symbolic)
            .with_location($ast.span())?;
        // .into_rr($ast.span(), [$ast.span(); $arity])?;
    };
}

fn parse_euf_cma<'str, 'bump, S>(
    env: &Environement<'bump, 'str, S>,
    functions: &[ast::Function<'str, S>],
    options: &Options<'str, S>,
    span: Location<'str>,
) -> MResult<CryptoAssumption<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    match functions.len() {
        2 => parse_uf_cma(env, functions, options, span),
        3 => {
            destvec!([ast_sign, ast_verify, ast_pk] = functions);
            verify_sign!(env; ast_sign, sign, EUF_CMA_SIGN_SIGNATURE, 2);
            verify_sign!(env; ast_verify, verify, EUF_CMA_VERIFY_SIGNATURE, 3);
            verify_sign!(env; ast_pk, pk, EUF_CMA_PK_SIGNATURE, 1);
            Ok(CryptoAssumption::EufCmaSign(EufCma { sign, verify, pk }))
        }
        i => span.bail_with(|| format!("wrong number of arguments: expected 2 or 3, got {i}")),
    }
}

fn parse_uf_cma<'str, 'bump, S>(
    env: &Environement<'bump, 'str, S>,
    functions: &[ast::Function<'str, S>],
    options: &Options<'str, S>,
    s: Location<'str>,
) -> MResult<CryptoAssumption<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let mut builder = UfCmaBuilder::default();
    if let [ast_mac, ast_verify] = functions {
        verify_sign!(env; ast_mac, mac, UF_CMA_MAC_SIGNATURE, 2);
        verify_sign!(env; ast_verify, verify, UF_CMA_VERIFY_SIGNATURE, 3);
        builder.mac(mac).verify(verify);
    } else {
        bail_at!(
            s,
            "wrong number of arguments: expected 2, got {:}",
            functions.len()
        )
    }
    if options.contains("hmac") {
        builder.hmac(true);
    }

    Ok(CryptoAssumption::UfCma(builder.build().unwrap()))
}

fn parse_int_ctxt<'str, 'bump, S>(
    env: &Environement<'bump, 'str, S>,
    functions: &[ast::Function<'str, S>],
    span: Location<'str>,
) -> MResult<CryptoAssumption<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let functions = match functions.len() {
        3 | 4 => Ok(&functions[..3]),
        i => span.bail_with(|| {
            format!(
                "wrong number of arguments: expected 3 \
        ('enc', 'dec' and 'fail'), got {i}"
            )
        }),
    }
    .debug_continue()?;
    destvec!([ast_enc, ast_dec, ast_fail] = functions);

    verify_sign!(env; ast_enc, enc, INT_CTXT_ENC_SIGNATURE, 3);
    verify_sign!(env; ast_dec, dec, INT_CTXT_DEC_SIGNATURE, 2);
    verify_sign!(env; ast_fail, fail, INT_CTXT_FAIL_SIGNATURE, 0);
    // verify_sign!(env; ast_verify, verify, INT_CTXT_VERIFY_SIGNATURE, 2);

    Ok(CryptoAssumption::IntCtxtSenc(IntCtxt { enc, dec, fail }))
}

fn parse_unfolding<'str, 'bump, S>(
    _env: &Environement<'bump, 'str, S>,
    functions: &[ast::Function<'str, S>],
    options: &Options<'str, S>,
    s: Location<'str>,
) -> MResult<CryptoAssumption<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    if !functions.is_empty() {
        bail_at!(s, "there should be no arguments")
    }

    let mut flags = Default::default();
    if options.contains("recurisve") {
        flags |= CryptoFlag::RECURSIVE_EXEC
    };
    // default
    if options.contains("direct") {
        flags |= CryptoFlag::DIRECT_EXEC
    };

    Ok(CryptoAssumption::Unfolding(Unfolding::new(flags)))
}
