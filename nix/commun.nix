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
            "steel-core-0.7.0" = "sha256-f60rAK6tIXk4LFDw+DbcY06NblmqalcJvWvbKYr9BHM=";
       };
        };
        src = lib.cleanSource src;
        patches = [ "${src}/nix.patch" ];
        buildInputs = [vampire];
      };
    in
    pkg
  );
}
