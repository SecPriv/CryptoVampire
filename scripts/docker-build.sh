#!/usr/bin/env bash
# Build a cryptovampire2 flake image target into an OCI tarball.
#
# Usage:
#   scripts/docker-build.sh <target> <output.tar.gz>
#
#   <target>      flake image output: `docker` or `docker-shell`
#   <output>      where to write the OCI tarball (e.g. docker/cryptovampire2-artifact)
#
# The build strategy is controlled by the IMAGE_BUILD environment variable
# (defaulting to `auto`):
#
#   auto      - use host nix if available, otherwise build inside a
#               nixos/nix container (the "chained docker" trick)
#   host      - always use host nix (nix build .#<target>)
#   container - always build inside nixos/nix; the host needs no nix,
#               only docker
#
# For container mode, how docker is invoked comes from the DOCKER environment
# variable (the Makefile sets it to a plain `docker` or a group-restricted
# `sudo -u $USER -g docker` command, see the Makefile).
#
# NOTE: container mode builds the whole closure into a cold nix store inside
# the container, so it needs ~15-25 GB of free disk, a few minutes to tens of
# minutes of CPU, and network for nix inputs.  Prefer `auto` (host nix, cached)
# or a pulled/pushed image; container mode is a fallback for machines that
# have neither nix nor a prebuilt image.
set -euo pipefail

target="${1:?flake target missing (docker|docker-shell)}"
out="${2:?output tarball path missing}"
mkdir -p "$(dirname -- "$out")"

mode="${IMAGE_BUILD:-auto}"

use_container=0
case "$mode" in
  container) use_container=1 ;;
  host)      use_container=0 ;;
  *)
    if command -v nix >/dev/null 2>&1; then
      use_container=0
    else
      use_container=1
    fi
    ;;
esac

if [ "$use_container" -eq 0 ]; then
  echo "[artifact] building .#${target} with host nix" >&2
  nix build ".#${target}" -o "result-${target}"
  cp -- "result-${target}" "$out"
else
  echo "[artifact] building .#${target} inside nixos/nix container (IMAGE_BUILD=${mode})" >&2
  # The container gets a *plain directory* snapshot of the repository (no git
  # metadata), built on the host where git is available -- this also works for
  # linked worktrees whose .git points outside the checkout.  The snapshot is
  # mounted read-only and built as a path flake, so no nix is needed on the
  # host at all, only docker.  Requires network for nix inputs.
  snap=$(mktemp -d /tmp/cv2-repo-XXXXXX)
  trap 'rm -rf -- "$snap"' EXIT
  git -C "$PWD" archive --format=tar HEAD 2>/dev/null | tar -xf - -C "$snap" \
    || { echo "[artifact] error: cannot snapshot the repository (git/tar?)" >&2; exit 1; }
  echo "[artifact] snapshot: $(git -C "$PWD" rev-parse --short HEAD) at $snap" >&2
  ${DOCKER:-docker} run --rm -v "$snap":/src:ro --workdir /tmp nixos/nix \
    sh -c "cd /src && nix build '.#${target}' -o /tmp/result --no-write-lock-file --extra-experimental-features 'nix-command flakes' 1>&2 && cat /tmp/result" \
    > "$out"
fi

echo "[artifact] wrote $out" >&2
