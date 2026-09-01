# OCI image derivations for the artifact evaluation.
#
# We produce self-contained OCI images via `dockerTools.buildImage`.  The
# reviewer *never* rebuilds cryptovampire2 and never needs nix, so the image
# deliberately contains:
#
#   - the prebuilt `cryptovampire2` release binary (from `.#cryptovampire2`)
#   - the SMT solvers (vampire-4 as in the dev shell, z3, cvc5)
#   - python3, make, bash, coreutils and friends (to run the harness Makefile)
#   - a *copy-on-first-run* snapshot of the source tree (cleanSource, ~15 MB)
#
# It does NOT contain a rust toolchain, cargo, or any nix infrastructure: the
# image is built *by* nix but works without nix at runtime.
#
# Two entrypoints are provided from the same layer set:
#
#   nix build .#docker          -> image whose default command runs
#                                   examples/cryptovampire2/Makefile `all`
#   nix build .#docker-shell    -> image that drops into a shell
#
# Load with:  docker load < result
{ self, inputs, lib, config, ... }:
{
  perSystem =
    { self', pkgs, system, config, ... }:
    let
      # ------------------------------------------------------------------
      # Contents of the image
      # ------------------------------------------------------------------

      # Snapshot of the source tree (git-tracked files only -> excludes
      # target/, result/, results/, .direnv/...; see .gitignore).
      src = lib.cleanSource self;



      binaries = [
          cryptovampire2 self'.packages.cryptovampire] ;

      cryptovampire2 = self'.packages.cryptovampire2;

      solvers =with pkgs;  [
        config.packages.vampire-4 # exactly what the dev shell exposes
        z3
        cvc5
      ];

      # Tools needed by the harness Makefile and the python test driver.
      tools = with pkgs; [
        bash
        coreutils
        gnumake
        python3
        git
        gnugrep
        gnused
        gawk
        findutils
        which
        diffutils
      ];

      # Merge everything into one `bin` (like `nix develop`'s PATH).  The
      # python driver also needs only the python3 stdlib, so plain python3 is
      # enough (no numpy/z3 python wrappers).
      env = pkgs.buildEnv {
        name = "cryptovampire2-env";
        paths = tools ++ solvers ++ binaries;
      };

      # The filesystem tree placed at the image root.  dockerTools packs the
      # whole closure of this derivation into the image's `/nix/store`, so the
      # image is fully self-contained at runtime (no nix daemon, no network).
      root = pkgs.runCommand "cryptovampire2-root" { } ''
        mkdir -p $out
        ln -s ${env}/bin $out/bin
        ln -s ${src} $out/cryptovampire2
        # Keep the entrypoint script in the packed closure (it is only listed
        # as a string in the image config, so it must also be reachable from
        # the root tree to end up in the layer).
        ln -s ${prepare} $out/prepare-workspace
        # The image has no base OS layer, so provide the standard writable
        # scratch dirs tools expect (tempfile/SMT sink, steel home parents),
        # plus a minimal /etc for user/group lookups (dockerTools.buildImage
        # has no enableFakeNss).
        mkdir -p $out/tmp/.local/share/steel $out/var/tmp $out/etc
        chmod 1777 $out/tmp $out/var/tmp
        cat > $out/etc/passwd <<EOF
root:x:0:0:root:/root:/bin/bash
nobody:x:65534:65534:nobody:/var/empty:/bin/false
EOF
        cat > $out/etc/group <<EOF
root:x:0:
nogroup:x:65534:
EOF
      '';

      # ------------------------------------------------------------------
      # Entrypoint: copy the (read-only, baked-in) source into a writable
      # /workspace on first run, point the harness at the prebuilt binary,
      # and hand over to the requested command.
      # ------------------------------------------------------------------
      prepare = pkgs.writeScript "cryptovampire2-prepare-workspace" ''
        #!/bin/sh
        set -e
        export PATH=/bin:/usr/bin
        export CV2_NO_BUILD=1   # harness Makefile: do not try to cargo-build
        if [ ! -e /workspace/cryptovampire2/Cargo.toml ]; then
          echo "[cryptovampire2] copying baked-in source to /workspace (one-time)..."
          mkdir -p /workspace/cryptovampire2
          cp -r /cryptovampire2/. /workspace/cryptovampire2/
        fi
        # (re)point the harness at the prebuilt binary so `make` has nothing to build
        mkdir -p /workspace/cryptovampire2/examples/cryptovampire2
        ln -sf ${cryptovampire2}/bin/cryptovampire2 \
               /workspace/cryptovampire2/examples/cryptovampire2/cryptovampire2
        cd /workspace/cryptovampire2/examples/cryptovampire2
        export HOME=/tmp
        echo "[cryptovampire2] ready in $(pwd)"
        echo "  make                        run all examples -> results/results.csv"
        echo "  make test-solvers-parallel  parallel solver matrix -> results/solver-test-results/"
        exec "$@"
      '';

      common = {
        copyToRoot = root;
        config = {
          Env = [
            "PATH=/bin:/usr/bin"
            "CV2_NO_BUILD=1"
            "HOME=/tmp"
          ];
        };
      };
                tag = "latest" ;# builtins.substring 0 8 self.rev or "dev";
    in
    {
      packages = {
        # `docker run <img>` -> runs the harness Makefile `all` target
        docker = pkgs.dockerTools.buildImage (common // {
          inherit tag;
          name = "cryptovampire2-artifact";
          config = common.config // {
            Cmd = [ "make" ];
            Entrypoint = [ "/prepare-workspace" ];
            WorkingDir = "/workspace/cryptovampire2/examples/cryptovampire2";
          };
        });

        # `docker run -it <img>` -> drops into a shell with all tools
        docker-shell = pkgs.dockerTools.buildImage (common // {
          inherit tag;
          name = "cryptovampire2-artifact-shell";
          config = common.config // {
            Cmd = [ "/bin/bash" "-i" ];
            Entrypoint = [ "/prepare-workspace" ];
            WorkingDir = "/workspace/cryptovampire2/examples/cryptovampire2";
          };
        });
      };
    };
}
