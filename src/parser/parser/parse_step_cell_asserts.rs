pub use step::parse_steps;
mod step;

pub use cells::parse_cells;
mod cells;

pub use asserts::*;
mod asserts;

pub use order::*;
mod order;

mod assert_crypto {
    use pest::Span;

    use crate::{
        destvec,
        environement::traits::Realm,
        formula::function::signature::{CheckError, Signature},
        parser::{
            ast, merr,
            parser::{get_function, Environement},
            IntoRuleResultFunction, E,
        },
        problem::crypto_assumptions::{
            CryptoAssumption, EufCmaMac, EufCmaSign, EUF_CMA_MAC_SIGNATURE, EUF_CMA_PK_SIGNATURE,
            EUF_CMA_SIGN_SIGNATURE, EUF_CMA_VERIFY_SIGNATURE,
        },
    };

    pub fn parse_assert_crypto<'str, 'bump>(
        env: &Environement<'bump, 'str>,
        crypto: &ast::AssertCrypto<'str>,
    ) -> Result<CryptoAssumption<'bump>, E> {
        let ast::AssertCrypto {
            span,
            name,
            functions,
        } = crypto;

        match name.content {
            "euf-cma" => parse_euf_cma(env, functions, *span),
            _ => Err(merr(name.span, "unknown crypto assertion".to_string())),
        }
    }

    macro_rules! verify_sign {
        ($env:ident; $ast:ident, $fun:ident, $signature:ident, $arity:literal) => {
            let $fun = *$env.find_function($ast.span(), $ast.name()).and_then(|f| {
                f.as_function().ok_or_else(|| {
                    merr($ast.span(), format!("{} should be a function", $ast.name()))
                })
            })?;
            $signature
                .as_ref()
                .unify(&$fun.signature(), &Realm::Symbolic)
                .into_rr($ast.span(), [$ast.span(); $arity])?;
        };
    }

    fn parse_euf_cma<'str, 'bump>(
        env: &Environement<'bump, 'str>,
        functions: &[ast::Function<'str>],
        span: Span<'str>,
    ) -> Result<CryptoAssumption<'bump>, E> {
        match functions.len() {
            2 => {
                destvec!([ast_mac, ast_verify] = functions);
                verify_sign!(env; ast_mac, mac, EUF_CMA_MAC_SIGNATURE, 2);
                verify_sign!(env; ast_verify, verify, EUF_CMA_VERIFY_SIGNATURE, 3);
                Ok(CryptoAssumption::EufCmaMac(EufCmaMac { mac, verify }))
            }
            3 => {
                destvec!([ast_sign, ast_verify, ast_pk] = functions);
                verify_sign!(env; ast_sign, sign, EUF_CMA_SIGN_SIGNATURE, 2);
                verify_sign!(env; ast_verify, verify, EUF_CMA_VERIFY_SIGNATURE, 3);
                verify_sign!(env; ast_pk, pk, EUF_CMA_PK_SIGNATURE, 1);
                Ok(CryptoAssumption::EufCmaSign(EufCmaSign {
                    sign,
                    verify,
                    pk,
                }))
            }
            i => Err(merr(
                span,
                format!("wrong number of arguments: expected 2 or 3, got {i}"),
            )),
        }
    }
}
