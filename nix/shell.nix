{ ... }:
{
  perSystem =
    { pkgs, config, ... }:
    let
      mpython = pkgs.python311.withPackages (
        ps: with ps; [
          numpy
          (toPythonModule pkgs.z3).python
        ]
      );

    in
    {
      devShells.default = config.devShells.rust.overrideAttrs (
        old: {
          buildInputs =
            old.buildInputs
            ++ (with pkgs; [
              mpython
              nixd
              graphviz
              lldb

              cvc5
              z3
              config.packages.vampire-4

              cargo-expand
              cargo-limit

            ]);
        }
      );

    };
}
