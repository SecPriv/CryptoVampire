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
    rust-flake = {
      url = "github:juspay/rust-flake";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    nixpkgs-vampire.url = "github:NixOS/nixpkgs/e0d5027e8873eaa5e8f74fba39072fcb231f4b4b";
    vampire-master-src = {
      url = "git+https://github.com/vprover/vampire.git?submodules=1";
      flake = false;
    };

    validator = {
      url = "github:puyral/delimiter-validator";
      inputs = {
        # nixpkgs.follows = "nixpkgs";
        treefmt-nix.follows = "treefmt-nix";
        flake-parts.follows = "flake-parts";
        rust-flake.follows = "rust-flake";
      };
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
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];

      perSystem =
        { system, ... }:
        {
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

}
