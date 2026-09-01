{ lib, self, ... }:
{
  perSystem =
    { config, ... }:
    {
      rust-project.src =
        let
          craneLib = config.rust-project.crane-lib;
          suffixes = [".txt" ".scm" ".pest" "/canauth.json" "/full1.json"];
        in
        lib.cleanSourceWith {
          src = self;
          filter =
            path: type:
            (craneLib.filterCargoSources path type)
            || builtins.any (s: lib.hasSuffix s path) suffixes
            ;
        };
    };
}
