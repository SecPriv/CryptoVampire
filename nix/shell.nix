{
  cryptovampire,
  mkShell,
  pkgs,
  rust,
  python311,
  z3,
  vampire,
  ...
}:
let

  toolchain = rust.toolchain;
  mrustPlatform = pkgs.makeRustPlatform {
    cargo = toolchain;
    rustc = toolchain;
  };

  mpython = python311.withPackages (
    ps: with ps; [
      numpy
      (toPythonModule z3).python
    ]
  );

in
mkShell {
  RUST_SRC_PATH = "${rust.rust-src}/lib/rustlib/src/rust/library/";

  buildInputs =
    with pkgs;
    cryptovampire.buildInputs
    ++ [
      mpython
      z3
      vampire
    ]
    ++ [
      nixd
      graphviz
      pest-ide-tools

      cvc5
      z3

      lldb
    ]
    ++ (with mrustPlatform; [
      bindgenHook
      cargoCheckHook
      cargoBuildHook
    ])
    ++ (with rust; [
      clippy
      rustc
      cargo
      rustfmt
      rust-analyzer
    ])
    ++ lib.optional stdenv.isDarwin git;
}
