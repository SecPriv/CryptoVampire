use std::env;
use std::path::Path;
use std::time::Duration;

use assert_cmd::{Command, cargo_bin};
use predicates::prelude::*;

#[test]
fn basic_hash() {
    mk_test("./tests/basic-hash.scm", &[]);
}

#[test]
fn lak_tag() {
    mk_test("./tests/lak-tag.scm", &[]);
}

#[test]
fn hash_lock() {
    mk_test("./tests/hash-lock.scm", &[]);
}

#[test]
fn mw() {
    mk_test("./tests/mw.scm", &[]);
}

#[test]
fn mw() {
    mk_test("./tests/ddh-P.scm", &[]);
}

fn mk_test(file: impl AsRef<Path>, extra_args: &[&str]) {
    let mut cmd = Command::new(cargo_bin!());
    cmd.pipe_stdin(file)
        .unwrap()
        .arg("--trace")
        .args(extra_args)
        .timeout(humantime::parse_duration("1h").unwrap())
        .assert()
        .success()
        .stdout(predicate::str::contains("success"));
}
