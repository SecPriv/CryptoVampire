{
  lib,
  callPackage,
  cryptovampire,
  cvc5,
  z3,
  vampire,
  test-dir ? ../tests/nix,
  treefmtEval,
  flake,
  ...
}:
with lib;
with builtins;
let
  files-match = map ({ name, ... }: match "(.*).ptcl" name) (attrsToList (readDir test-dir));
  files = filter (name: (name != null) && (name != [ ])) files-match;
  basenames = map head files;
  check = name: {
    inherit name;
    value = callPackage test-dir {
      inherit
        cryptovampire
        cvc5
        z3
        vampire
        name
        ;
      file = "${test-dir}/${name}.ptcl";
    };
  };
  auto-checks = listToAttrs (map check basenames);
in
{
  # formatting = treefmtEval.config.build.check flake;
}
// auto-checks
