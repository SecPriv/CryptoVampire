{ inputs, ... }:
{
  perSystem =
    {
      self',
      pkgs,
      system,
      ...
    }:
    {
      packages = {
        default = self'.packages.indistinguishability;
        vampire-master = pkgs.vampire.overrideAttrs (oldAttrs: {
          src = inputs.vampire-master-src;
        });
        vampire-4 = (import inputs.nixpkgs-vampire { inherit system; }).vampire;
      };

      # apps.default = self'.apps.indistinguishability;

    };
}
