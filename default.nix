{ lib, rustPlatform, src ? ./. }:

let
  manifest = (lib.importTOML "${src}/crates/cryptovampire/Cargo.toml").package;
  cryptovampire = rustPlatform.buildRustPackage {
    name = manifest.name;
    version = manifest.version;
    cargoLock.lockFile = "${src}/Cargo.lock";
    src = lib.cleanSource src;
    patches = [ "${src}/nix.patch" ];
  };
in cryptovampire
