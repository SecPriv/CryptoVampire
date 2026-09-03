{
  inputs,
  lib,
  self,
  ...
}:
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
        default = self'.packages.cryptovampire2;
        vampire-master = pkgs.vampire.overrideAttrs (oldAttrs: {
          src = inputs.vampire-master-src;
        });
        vampire-4 = (import inputs.nixpkgs-vampire { inherit system; }).vampire;

        # API documentation as a nix package.  This reproduces the doc recipe
        # WITHOUT calling the Makefile: it reuses the already-built
        # `cryptovampire2` binary (packages.cryptovampire2), runs
        # the scheme docgen into `docs/scheme-api.md`, then renders that
        # markdown as an HTML book with mdBook.  Outputs:
        #   $out/scheme-api.md   the markdown reference
        #   $out/book/           the HTML book (e.g. $out/book/index.html)
        doc = pkgs.stdenv.mkDerivation {
          pname = "cryptovampire-api-doc";
          version = "0.1.0";
          src = lib.cleanSourceWith {
            src = self;
            filter =
              path: type:
              !(builtins.elem (baseNameOf path) [
                "target"
                "out"
                "result"
                "book"
                ".direnv"
              ]);
          };
          nativeBuildInputs = with pkgs; [
            mdbook
            self'.packages.cryptovampire2
          ];
          buildPhase = ''
            export HOME="$TMPDIR"
            mkdir -p "$out"
            # run the scheme docgen against the built binary (the `make doc` step)
            cryptovampire2 ./crates/cryptovampire2/scheme/docgen.scm
            cp ./docs/scheme-api.md "$out/"
            # render the markdown as an HTML book (the `make html` step)
            mdbook build ./docs
            cp -r ./docs/book "$out/book"
          '';
          installPhase = "true";
          meta = with pkgs.lib; {
            description = "CryptoVampire API documentation (markdown + mdBook html)";
            platforms = platforms.linux;
          };
        };
        api-doc = self'.packages.doc;
      };

      # apps.default = self'.apps.cryptovampire2;

    };
}
