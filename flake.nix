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
  };

  outputs = inputs@{ self, nixpkgs, flake-utils, custom, nix2container, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        src = ./crates/cryptovampire;
        custom-pkgs = custom.packages.${system};
        manifest = (pkgs.lib.importTOML "${src}/Cargo.toml").package;

        my-z3 = pkgs.z3.overrideAttrs (finalAttrs: previousAttrs: {
          src = pkgs.fetchFromGitHub {
            owner = "Z3Prover";
            repo = "z3";
            rev = "z3-4.13.4";
            sha256 = "sha256-8hWXCr6IuNVKkOegEmWooo5jkdmln9nU7wI8T882BSE=";
          };
          version = "4.13.4";
          doCheck = false;
        });
        my-vampire = custom-pkgs.vampire;

        my-python = pkgs.python311.withPackages
          (ps: with ps; [ numpy (toPythonModule my-z3).python ]);

        mrustPlateform = pkgs.rustPlatform;

        cryptovampire = pkgs.callPackage ./default.nix {
          rustPlatform = mrustPlateform;
          src = ./.;
        };

        defaultDevShell = pkgs.mkShell {
          RUST_SRC_PATH = "${mrustPlateform.rustLibSrc}";

          buildInputs = with pkgs;
            cryptovampire.buildInputs ++ [
              lldb
              cargo
              cargo-expand
              rustc
              nixd
              my-z3
              cvc5
              my-vampire
              # custom-pkgs.squirrel-prover
              rustfmt
              clippy
              rust-analyzer
              my-python
              graphviz
            ] ++ lib.optional stdenv.isDarwin git;
        };

        test-dir = ./tests/nix;

        auto-checks = with pkgs.lib;
          with builtins;
          let
            tools = with pkgs; {
              inherit cryptovampire cvc5;
              vampire = my-vampire;
              z3 = my-z3;
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
        doc = pkgs.callPackage ./doc.nix { inherit cryptovampire; };

      in rec {
        packages = {
          inherit cryptovampire;
          default = cryptovampire;
        };
        checks = auto-checks;
        formatter = nixpkgs.legacyPackages.${system}.nixfmt;

        devShells.default = defaultDevShell;

        apps = rec {
          default = cryptovampire;
          cryptovampire =
            flake-utils.lib.mkApp { drv = packages.cryptovampire; };
        };
      });

}
