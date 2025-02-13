{
  mkPkg =(manifestFile: { lib, rustPlatform, src ? ./.. }:

let
  manifest = (lib.importTOML manifestFile).package;
  pkg = rustPlatform.buildRustPackage {
    name = manifest.name;
    version = manifest.version;
    cargoLock.lockFile = "${src}/Cargo.lock";
    src = lib.cleanSource src;
    patches = [ "${src}/nix.patch" ];
  };
in pkg);
}