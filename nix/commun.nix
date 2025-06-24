{
  mkPkg = (
    manifestFile:
    {
      lib,
      rustPlatform,
      src ? ./..,
    }:

    let
      manifest = (lib.importTOML manifestFile).package;
      pkg = rustPlatform.buildRustPackage {
        name = manifest.name;
        version = manifest.version;
        cargoLock = {
          lockFile = "${src}/Cargo.lock";

          outputHashes = {
         "steel-core-0.6.0" = "sha256-x1DE5D8MlA344AZQMUq/xh8LqPZ0vEhzWYhIO2gFzTs=";
       };
        };
        src = lib.cleanSource src;
        patches = [ "${src}/nix.patch" ];
      };
    in
    pkg
  );
}
