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
        src = ./cryptovampire;
        custom-pkgs = custom.packages.${system};
        manifest = (pkgs.lib.importTOML "${src}/Cargo.toml").package;

        my-z3 = pkgs.z3;

        my-python = pkgs.python311.withPackages
          (ps: with ps; [ numpy (toPythonModule my-z3).python ]);

        mrustPlateform = pkgs.rustPlatform;

        cryptovampire = mrustPlateform.buildRustPackage {
          name = manifest.name;
          version = manifest.version;
          cargoLock.lockFile = ./Cargo.lock;
          src = pkgs.lib.cleanSource ./.;
          patches = [ ./nix.patch ];
        };

        defaultDevShell = pkgs.mkShell {
          RUST_SRC_PATH = "${mrustPlateform.rustLibSrc}";

          buildInputs = with pkgs;
            cryptovampire.buildInputs ++ [
              cargo
              rustc
              nil
              z3
              cvc5
              custom-pkgs.vampire-master
              rustfmt
              clippy
              rust-analyzer
              my-python
              graphviz
            ];
        };

        dockerShell_old = pkgs.mkShell {
          buildInputs = [ cryptovampire ]
            ++ (with custom-pkgs; [ squirrel-prover vampire ])
            ++ (with pkgs; [ z3 cvc5 emacs vim ]);
          shellHook = ''
            export PAHT=PATH:${custom-pkgs.squirrel-prover}
            export CRYTPOVAMPIRE_LOCATION=${cryptovampire}/bin/cryptovampire
          '';
        };


        dockerImage = with nix2container.packages.${system}.nix2container; buildImage {
          name = "cryptovampire";
          layers = let
            commonLayer = {
              deps = with pkgs; [
                bashInteractive
                emacs
                vim
                z3
                cvc5
                custom-pkgs.vampire
              ];
            };
            layerDefs = [
              {
                deps = [ custom-pkgs.squirrel-prover ];
                layers = [ (buildLayer commonLayer) ];
              }
              {
                deps = [ cryptovampire ];
                layers = [ (buildLayer commonLayer) ];
              }
            ];
          in builtins.map buildLayer layerDefs;
          config = {
            Env = [
              (let
                path = with pkgs;
                  lib.makeBinPath [
                    bashInteractive
                    custom-pkgs.squirrel-prover
                    cryptovampire
                    emacs
                    vim
                    z3
                    cvc5
                  ];
              in "PATH=${path}:${custom-pkgs.squirrel-prover}")
              "CRYTPOVAMPIRE_LOCATION=${cryptovampire}/bin/cryptovampire"
            ];
            Entrypoint = ["bash"];
          };
        };

      in rec {
        packages = { inherit cryptovampire dockerImage; };
        formatter = nixpkgs.legacyPackages.${system}.nixfmt;

        devShell = defaultDevShell;

        defaultPackage = packages.cryptovampire;
        apps.cryptovampire =
          flake-utils.lib.mkApp { drv = packages.cryptovampire; };
        defaultApp = apps.cryptovampire;
      });

}
