{
  mkPkg = (
    manifestFile:
    {
      lib,
      rustPlatform,
      src ? ./..,
      vampire,
    }:

    let
      manifest = (lib.importTOML manifestFile).package;
      pkg = rustPlatform.buildRustPackage {
        name = manifest.name;
        version = manifest.version;
        cargoLock = {
          lockFile = "${src}/Cargo.lock";

          outputHashes = {
            "steel-core-0.8.2" = "sha256-G3hWh/AIfvAyAbCG6j/EWKeBsPOk9bMpV5ko+UPu2p4";
          };
        };
        src = lib.cleanSource src;
        patches = [ "${src}/nix.patch" ];
        buildInputs = [ vampire ];
        doCheck = false;
      };
    in
    pkg
  );
}
