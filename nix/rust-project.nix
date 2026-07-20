{ lib, self, ... }: {
  perSystem = { config, ... }: {
    rust-project.src =
      let
        craneLib = config.rust-project.crane-lib;
      in
      lib.cleanSourceWith {
        src = self;
        filter = path: type:
          (craneLib.filterCargoSources path type)
          || (lib.hasSuffix ".txt" path)
          || (lib.hasSuffix ".scm" path);
      };
  };
}
