{
  description = "cryptovampire";

  # nixConfig = {
  #   extra-substituters = [
  #     "https://nix-community.cachix.org"
  #   ];
  #   extra-trusted-public-keys = [
  #     "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs="
  #   ];
  # };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils = {
      url = "github:numtide/flake-utils";
    };

    rust-overlay= {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    custom = {
      url = "github:puyral/custom-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.squirrel-prover-src.url = "github:puyral/squirrel-prover?ref=cryptovampire";
      inputs.cryptovampire-src.url = "github:puyral/empty-flake";
      inputs.vampire-master-src.url = "github:vprover/vampire";
    };
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # fenix = {
    #   url = "github:nix-community/fenix/monthly";
    #   inputs.nixpkgs.follows = "nixpkgs";
    # };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      custom,
      treefmt-nix,
      # fenix,
      rust-overlay,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        custom-pkgs = custom.packages.${system};
        treefmtEval = treefmt-nix.lib.evalModule pkgs ./nix/fmt.nix;

        # rust = fenix.packages.${system}.complete;
        # toolchain = rust.toolchain;
        use-nightly = false;

        rustPlatform =
          # if use-nightly then
          #   pkgs.makeRustPlatform {
          #     cargo = toolchain;
          #     rustc = toolchain;
          #   }
          # else
            pkgs.rustPlatform;

        pkgConfig = {
          inherit rustPlatform;
          src = ./.;
        };

        cryptovampire = pkgs.callPackage ./crates/cryptovampire/default.nix pkgConfig;
        indistinguishability = pkgs.callPackage ./crates/indistinguishability/default.nix pkgConfig;
        doc = pkgs.callPackage ./nix/doc.nix { inherit cryptovampire; };

        # mrust = if use-nightly then rust else pkgs;
        mrust =  pkgs;

      in
      rec {
        packages = {
          inherit cryptovampire indistinguishability;
          default = indistinguishability;
        };
        checks =
          let
            checks = pkgs.callPackage ./nix/check.nix {
              inherit cryptovampire treefmtEval;
              flake = self;
            };
            cleanUp =
              checks:
              builtins.removeAttrs checks [
                "override"
                "overrideDerivation"
              ];
          in
          cleanUp checks;

        formatter = treefmtEval.config.build.wrapper;

        devShells.default = pkgs.callPackage ./nix/shell.nix (
          with mrust;
          {
            inherit
              cryptovampire
              indistinguishability
              clippy
              rustc
              cargo
              rustfmt
              rust-analyzer
              rustPlatform
              ;
          }
        );

        apps = rec {
          default = indistinguishability;
          cryptovampire = flake-utils.lib.mkApp { drv = packages.cryptovampire; };
          indistinguishability = flake-utils.lib.mkApp { drv = packages.indistinguishability; };
        };
      }
    );

}
