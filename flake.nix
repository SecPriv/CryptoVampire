{
  description = "cryptovampire";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils = { url = "github:numtide/flake-utils"; };
    custom = {
      url = "github:puyral/custom-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.squirrel-prover-src.url =
        "github:puyral/squirrel-prover?ref=cryptovampire";
      # inputs.cryptovampire-src.url = ".";
      inputs.vampire-master-src.url = "github:vprover/vampire";
    };
    nix2container = {
      url = "github:nlewo/nix2container?ref=update-patch-hash";
      inputs.nixpkgs.follows = "nixpkgs";
    };
        treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-utils, custom, nix2container, treefmt-nix, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        custom-pkgs = custom.packages.${system};
        treefmtEval = treefmt-nix.lib.evalModule pkgs ./fmt.nix;

        my-z3 = pkgs.z3_4_12;
		mvampire = custom-pkgs.vampire.override {z3=my-z3;};

        my-python = pkgs.python311.withPackages
          (ps: with ps; [ numpy (toPythonModule my-z3).python ]);

        mrustPlateform = pkgs.rustPlatform;

        pkgConfig = {
          rustPlatform = mrustPlateform;
          src = ./.;
        };

        cryptovampire = pkgs.callPackage ./crates/cryptovampire/default.nix pkgConfig;
        egg = pkgs.callPackage ./crates/indistinguishability/default.nix pkgConfig;

        defaultDevShell = pkgs.mkShell {
          RUST_SRC_PATH = "${mrustPlateform.rustLibSrc}";

          buildInputs = with pkgs;
            cryptovampire.buildInputs ++ [
              lldb
              cargo
              cargo-expand
              rustc
              nixd
              #my-z3
              cvc5
              #mvampire
              # custom-pkgs.squirrel-prover
              rustfmt
              clippy
              rust-analyzer
              # my-python
              graphviz
            ] ++ lib.optional stdenv.isDarwin git;
        };

        test-dir = ./tests/nix;

        auto-checks = with pkgs.lib;
          with builtins;
          let
            tools = with pkgs; {
              inherit cryptovampire z3 cvc5;
              vampire = mvampire;
            };
            files-match = map ({ name, ... }: match "(.*).ptcl" name)
              (attrsToList (readDir test-dir));
            files = filter (name: (name != null) && (name != [ ])) files-match;
            basenames = map head files;
            check = basename: {
              name = basename;
              value = pkgs.callPackage test-dir (tools // {
                file = "${test-dir}/${basename}.ptcl";
                name = basename;
              });
            };
          in listToAttrs (map check basenames);
        doc = pkgs.callPackage ./nix/doc.nix {inherit cryptovampire;};

      in rec {
        packages = {
          inherit cryptovampire egg ;
          default = cryptovampire;
        };
        checks = {
          formatting = treefmtEval.config.build.check self;
        } // auto-checks;
        formatter = treefmtEval.config.build.wrapper;

        devShells.default = defaultDevShell;

        apps = rec {
          default = cryptovampire;
          cryptovampire =
            flake-utils.lib.mkApp { drv = packages.cryptovampire; };
        };
      });

}
