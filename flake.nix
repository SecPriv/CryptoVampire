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

    nixpkgs-vampire.url ="github:NixOS/nixpkgs/e0d5027e8873eaa5e8f74fba39072fcb231f4b4b";

    flake-utils = {
      url = "github:numtide/flake-utils";
    };

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # fenix = {
    #   url = "github:nix-community/fenix/monthly";
    #   inputs.nixpkgs.follows = "nixpkgs";
    # };

    vampire-master-src = {
      url = "git+https://github.com/vprover/vampire.git?submodules=1";
      flake = false;
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      nixpkgs-vampire,
      flake-utils,
      treefmt-nix,
      # fenix,
      rust-overlay,
      vampire-master-src,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        vampire-master-overlay = final: prev: {
          vampire = prev.vampire.overrideAttrs (oldAttrs: {
            src = vampire-master-src;
          });
        };
        vampire-4-overlay = final: prev: {
          vampire = pkgs-vampire.vampire;
        };
        overlays = [
          (import rust-overlay)
          vampire-4-overlay 
          # vampire-overlay
        ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        pkgs-vampire = import nixpkgs-vampire {inherit system; };
        treefmtEval = treefmt-nix.lib.evalModule pkgs ./nix/fmt.nix;

        # rust = fenix.packages.${system}.complete;
        # toolchain = rust.toolchain;
        use-nightly = true;
        rust =
          with pkgs;
          if use-nightly then
            rust-bin.selectLatestNightlyWith (toolchain: toolchain.complete)
          # rust-bin.stable.minimal;
          else
            rust-bin.stable.latest.complete;

        # rustPlatform =
        #   # if use-nightly then
        #   #   pkgs.makeRustPlatform {
        #   #     cargo = toolchain;
        #   #     rustc = toolchain;
        #   #   }
        #   # else
        #   pkgs.rustPlatform;
        rustPlatform = pkgs.makeRustPlatform {
          cargo = rust;
          rustc = rust;
        };

        pkgConfig = {
          inherit rustPlatform;
          src = ./.;
        };

        cryptovampire = pkgs.callPackage ./crates/cryptovampire/default.nix pkgConfig;
        indistinguishability = pkgs.callPackage ./crates/indistinguishability/default.nix pkgConfig;
        doc = pkgs.callPackage ./nix/doc.nix { inherit cryptovampire; };

        # mrust = if use-nightly then rust else pkgs;
        mrust = pkgs;

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

        devShells.default = pkgs.callPackage ./nix/shell.nix ({
          inherit
            cryptovampire
            indistinguishability
            rust
            rustPlatform
            ;
        });

        apps = rec {
          default = indistinguishability;
          cryptovampire = flake-utils.lib.mkApp { drv = packages.cryptovampire; };
          indistinguishability = flake-utils.lib.mkApp { drv = packages.indistinguishability; };
        };
      }
    );

}
