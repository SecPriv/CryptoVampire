{
  description = "cryptovampire";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils = { url = "github:numtide/flake-utils"; };
    custom = {url = "github:puyral/custom-nix"; inputs.nixpkgs.follows = "nixpkgs";};
  };

  outputs = inputs@{ self, nixpkgs, flake-utils, custom, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        src = ./cryptovampire;
	custom-pkgs = custom.packages.${system};
        manifest = (pkgs.lib.importTOML "${src}/Cargo.toml").package;
      in rec {
        packages.cryptovampire = pkgs.rustPlatform.buildRustPackage {
          name = manifest.name;
          version = manifest.version;
          cargoLock.lockFile = ./Cargo.lock;
          src = pkgs.lib.cleanSource ./.;
          patches = [ ./nix.patch ];
        };
        formatter = nixpkgs.legacyPackages.${system}.nixfmt;

        devShell = pkgs.mkShell {
          RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";

          buildInputs = with pkgs;
            defaultPackage.buildInputs
            ++ [ cargo rustc nil z3 cvc5 custom-pkgs.vampire-master rustfmt clippy rust-analyzer ];
        };

        defaultPackage = packages.cryptovampire;
        apps.cryptovampire =
          flake-utils.lib.mkApp { drv = packages.cryptovampire; };
        defaultApp = apps.cryptovampire;
      });

}
