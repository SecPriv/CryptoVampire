{
  cryptovampire,
  indistinguishability,
  mkShell,
  pkgs,
  python311,
  z3,
  vampire,
  rustPlatform,
  rust,
  ...
}:
let

  mpython = python311.withPackages (
    ps: with ps; [
      numpy
      (toPythonModule z3).python
    ]
  );

in
mkShell {
  buildInputs =
    with pkgs;
    cryptovampire.buildInputs
    ++ indistinguishability.buildInputs
    ++ [
      mpython
      nixd
      graphviz
      # pest-ide-tools
      lldb

      cvc5
      z3
      vampire

      cargo-expand
      cargo-limit
      rust
    ]
    ++ (with rustPlatform; [
      bindgenHook
      cargoCheckHook
      cargoBuildHook
    ])
    ++ lib.optional stdenv.isDarwin git;
}
