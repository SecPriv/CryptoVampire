use std::{env, path::Path};

use assert_cmd::{Command, cargo_bin};
use predicates::prelude::*;

#[test]
fn basic_hash() {
    mk_test("./tests/basic-hash.scm", &[]);
}

#[test]
fn lak_tag() {
    mk_test(
        "./tests/lak-tag.scm",
        &[
            "--vampire-timeout",
            "3s",
            "--node-limit",
            "100000",
            "--prf-limit",
            "1",
        ],
    );
}

fn mk_test(file: impl AsRef<Path>, extra_args: &[&str]) {
    let mut cmd = Command::new(cargo_bin!());
    cmd.pipe_stdin(file).unwrap();
    cmd.args(extra_args);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("success"));
}
