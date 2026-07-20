{
  description = "cryptovampire";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";


    flake-utils = {
      url = "github:numtide/flake-utils";
    };

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
    };
    rust-flake={
      url = "github:juspay/rust-flake";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    nixpkgs-vampire.url ="github:NixOS/nixpkgs/e0d5027e8873eaa5e8f74fba39072fcb231f4b4b";
    vampire-master-src = {
      url = "git+https://github.com/vprover/vampire.git?submodules=1";
      flake = false;
    };
  };

  outputs =
    inputs@{
      flake-parts,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } (attrs: {
        imports = [
          ./nix
          inputs.rust-flake.flakeModules.default
          inputs.rust-flake.flakeModules.nixpkgs
          inputs.treefmt-nix.flakeModule
        ];

        # TODO add more
        systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];

        perSystem = { system, ... }: {
          # Set nixpkgs.pkgs directly to avoid an infinite recursion in
          # nixpkgs.nix's configType.merge, which forces `pkgs` while `pkgs`
          # is being defined by the same module via _module.args.pkgs.
          nixpkgs.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ (import inputs.rust-flake.inputs.rust-overlay) ];
            config = { };
          };
        };
    });


    # flake-utils.lib.eachDefaultSystem (
    #   system:
    #   let
    #     vampire-master-overlay = final: prev: {
    #       vampire = prev.vampire.overrideAttrs (oldAttrs: {
    #         src = vampire-master-src;
    #       });
    #     };
    #     vampire-4-overlay = final: prev: {
    #       vampire = pkgs-vampire.vampire;
    #     };
    #     overlays = [
    #       (import rust-overlay)
    #       vampire-4-overlay 
    #       # vampire-overlay
    #     ];
    #     pkgs = import nixpkgs {
    #       inherit system overlays;
    #     };
    #     pkgs-vampire = import nixpkgs-vampire {inherit system; };
    #     treefmtEval = treefmt-nix.lib.evalModule pkgs ./nix/fmt.nix;

    #     # rust = fenix.packages.${system}.complete;
    #     # toolchain = rust.toolchain;
    #     use-nightly = true;
    #     rust =
    #       with pkgs;
    #       if use-nightly then
    #         rust-bin.selectLatestNightlyWith (toolchain: toolchain.complete)
    #       # rust-bin.stable.minimal;
    #       else
    #         rust-bin.stable.latest.complete;

    #     rustPlatform = pkgs.makeRustPlatform {
    #       cargo = rust;
    #       rustc = rust;
    #     };

    #     pkgConfig = {
    #       inherit rustPlatform;
    #       src = ./.;
    #     };

    #     cryptovampire = pkgs.callPackage ./crates/cryptovampire/default.nix pkgConfig;
    #     indistinguishability = pkgs.callPackage ./crates/indistinguishability/default.nix pkgConfig;
    #     doc = pkgs.callPackage ./nix/doc.nix { inherit cryptovampire; };

    #     # mrust = if use-nightly then rust else pkgs;
    #     mrust = pkgs;

    #   in
    #   rec {
    #     packages = {
    #       inherit cryptovampire indistinguishability;
    #       default = indistinguishability;
    #     };
    #     checks =
    #       let
    #         checks = pkgs.callPackage ./nix/check.nix {
    #           inherit cryptovampire treefmtEval;
    #           flake = self;
    #         };
    #         cleanUp =
    #           checks:
    #           builtins.removeAttrs checks [
    #             "override"
    #             "overrideDerivation"
    #           ];
    #       in
    #       cleanUp checks;

    #     formatter = treefmtEval.config.build.wrapper;

    #     devShells.default = pkgs.callPackage ./nix/shell.nix ({
    #       inherit
    #         cryptovampire
    #         indistinguishability
    #         rust
    #         rustPlatform
    #         ;
    #     });

    #     apps = rec {
    #       default = indistinguishability;
    #       cryptovampire = flake-utils.lib.mkApp { drv = packages.cryptovampire; };
    #       indistinguishability = flake-utils.lib.mkApp { drv = packages.indistinguishability; };
    #     };
    #   }
    # );

}
