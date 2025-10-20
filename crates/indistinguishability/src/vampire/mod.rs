mod base_axioms;
pub use base_axioms::mk_prelude;
pub mod runner;

#[cfg(test)]
mod test {
    use cryptovampire_macros::smt;
    use cryptovampire_smt::SmtFormula;

    // #[test]
    // fn test_smt_macro() {
    //     let x = 2;
    //     let f = "t";
    //     let t: SmtFormula<&'static str, &'static str> = smt! {
    //         (forall ((#a!x "my_sort")) (f #a #a))
    //     };
    //     println!("{t}")
    // }
}
