OUT_DIR := ./out
PROJECT_DIR := .
BUILD_DIR := $(PROJECT_DIR)/target/release

CRYPTOVAMPIRE2 := $(OUT_DIR)/cryptovampire2
CRYPTOVAMPIRE := $(OUT_DIR)/cryptovampire

BOOK_DIR := $(PROJECT_DIR)/docs

.PHONY: cryptovampire2 cryptovampire doc html

cryptovampire2:
	mkdir -p $(OUT_DIR)
	cargo build --release -p cryptovampire2
	cp $(BUILD_DIR)/cryptovampire2 $(CRYPTOVAMPIRE2)

cryptovampire:
	cargo build --release -p cryptovampire
	cp $(BUILD_DIR)/cryptovampire $(CRYPTOVAMPIRE)

doc: cryptovampire2 $(PROJECT_DIR)/crates/cryptovampire2/scheme/docgen.scm
	mkdir -p $(OUT_DIR)
	$(CRYPTOVAMPIRE2) $(PROJECT_DIR)/crates/cryptovampire2/scheme/docgen.scm
	cp $(PROJECT_DIR)/docs/scheme-api.md $(OUT_DIR)

# HTML book of the API reference, rendered from the markdown with mdBook
# (docs/book.toml + docs/SUMMARY.md).  mdBook must already be on PATH (e.g.
# from `nix develop`); this Makefile deliberately does not install it.
html: doc
	mdbook build $(BOOK_DIR)
	mkdir -p $(OUT_DIR)
	rm -rf $(OUT_DIR)/book
	cp -r $(BOOK_DIR)/book $(OUT_DIR)

# ===========================================================================
# Docker artifact shortcuts
#
# DOCKER       how to invoke docker (a full runner prefix that ends with the
#              `docker` command): plain `docker` when the current user is
#              already in the docker group; otherwise (via sudo) run as the
#              current user with only the docker group added for the duration
#              of the command -- i.e. NOT full root.  Override if needed, e.g.
#                  make test-artifact DOCKER="sudo docker"
#              (or add yourself to the docker group once; on NixOS that is
#              users.users.<name>.extraGroups = [ "docker" ] + nixos-rebuild).
#
# IMAGE_BUILD  how a flake image target is turned into an OCI tarball in docker/:
#                auto      - use host nix if available, else build inside the
#                            nixos/nix container (default)
#                host      - always use host nix (nix build ...)
#                container - always build inside nixos/nix; the host needs no
#                            nix, only docker (the "chained docker" trick)
# ===========================================================================

DOCKER_GROUP    ?= docker
IN_DOCKER_GROUP := $(shell id -nG 2>/dev/null | tr ' ' '\n' | grep -qx $(DOCKER_GROUP) && echo 1 || echo 0)
ifeq ($(IN_DOCKER_GROUP),1)
DOCKER ?= docker
else
DOCKER ?= sudo -u $(shell id -un) -g $(DOCKER_GROUP) docker
endif

IMAGE_BUILD  ?= auto

SOLVER_ARGS ?= FILES="basic-hash.scm ddh-P.scm" CONFIGS="no-vampire z3-only"

# Rebuild the image every time (the binary/source is baked in, and nix makes
# an up-to-date rebuild nearly free); FORCE disables make's file-time shortcut.
FORCE:

docker/cryptovampire2-artifact: FORCE
	IMAGE_BUILD=$(IMAGE_BUILD) DOCKER="$(DOCKER)" ./scripts/docker-build.sh docker $@

docker/cryptovampire2-artifact-shell: FORCE
	IMAGE_BUILD=$(IMAGE_BUILD) DOCKER="$(DOCKER)" ./scripts/docker-build.sh docker-shell $@

.PHONY: test-artifact test-solvers-parallel enter-shell FORCE

test-artifact: docker/cryptovampire2-artifact
	@mkdir -p results
	$(DOCKER) load < docker/cryptovampire2-artifact
	$(DOCKER) run --rm -v $(CURDIR)/results:/workspace/cryptovampire2/examples/cryptovampire2/results cryptovampire2-artifact

test-solvers-parallel: docker/cryptovampire2-artifact
	@mkdir -p results
	$(DOCKER) load < docker/cryptovampire2-artifact
	$(DOCKER) run --rm -v $(CURDIR)/results:/workspace/cryptovampire2/examples/cryptovampire2/results \
		cryptovampire2-artifact make test-solvers-parallel $(SOLVER_ARGS)

enter-shell: docker/cryptovampire2-artifact-shell
	@mkdir -p results
	$(DOCKER) load < docker/cryptovampire2-artifact-shell
	$(DOCKER) run --rm -it -v $(CURDIR)/results:/workspace/cryptovampire2/examples/cryptovampire2/results cryptovampire2-artifact-shell