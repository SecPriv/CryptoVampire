use std::env;
use std::path::Path;
use std::time::Duration;

use assert_cmd::{Command, cargo_bin};
use predicates::prelude::*;

static BASE_DIR: &str = "./tests/passing";

#[test]
fn basic_hash() {
    mk_test(format!("{BASE_DIR}/basic-hash.scm"), &[]);
}

#[test]
fn lak_tag() {
    mk_test(format!("{BASE_DIR}/lak-tag.scm"), &[]);
}

#[test]
fn hash_lock() {
    mk_test(format!("{BASE_DIR}/hash-lock.scm"), &[]);
}

#[test]
fn mw() {
    mk_test(format!("{BASE_DIR}/mw.scm"), &[]);
}

#[test]
#[allow(non_snake_case)]
fn ddh() {
    mk_test(format!("{BASE_DIR}/ddh-P.scm"), &[]);
    mk_test(format!("{BASE_DIR}/ddh-S.scm"), &[]);
}

#[test]
fn private_authentication() {
    mk_test(format!("{BASE_DIR}/private-auth.scm"), &[]);
}

#[test]
fn feldhofer() {
    mk_test(format!("{BASE_DIR}/feldhofer.scm"), &[]);
}

fn mk_test(file: impl AsRef<Path>, extra_args: &[&str]) {
    let mut cmd = Command::new(cargo_bin!());
    cmd.arg("--trace")
        .args(extra_args)
        .args(["file", file.as_ref().to_str().unwrap()])
        .timeout(humantime::parse_duration("1h").unwrap())
        .assert()
        .success()
        .stdout(predicate::str::contains("success"));
}
