# CryptoVampire2 — artifact evaluation reviewer Makefile
#
# This Makefile needs NO nix.  The only requirement is docker (or podman) and
# `make`.  It drives the prebuilt OCI images that contain the cryptovampire2
# binary, the SMT solvers (vampire/z3/cvc5), python/make and a snapshot of this
# repository, so reviewers can run the full example suite and the parallel
# solver matrix without compiling anything.
#
# The images are built with nix by the authors (see docker/README.md); once a
# registry is set (REGISTRY=...), `make pull` fetches them.

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

# Registry/repo prefix of the prebuilt images.  Leave unset to use the locally
# loaded images (docker build/load by hand or `make build-nix`).
REGISTRY   ?=
IMAGE      := cryptovampire2-artifact
SHELL_IMAGE:= cryptovampire2-artifact-shell
TAG        ?= dev

# Host directory that receives the results (results.csv, solver-test-results/).
RESULTS_DIR ?= $(CURDIR)/results

# Working directory inside the container (the harness Makefile's directory).
WORKDIR := /workspace/cryptovampire2/examples/cryptovampire2

FULL_IMAGE := $(if $(REGISTRY),$(REGISTRY)/$(IMAGE):$(TAG),$(IMAGE):$(TAG))

# Quick default for the parallel matrix (override with SOLVER_ARGS="..." or
# these pass through to the Makefile target inside the container).
SOLVER_ARGS ?= FILES="basic-hash.scm ddh-P.scm" CONFIGS="no-vampire z3-only"

VOLUME_ARGS := -v $(RESULTS_DIR):$(WORKDIR)/results

.PHONY: help pull run test-solvers-parallel shell build-nix results

help:
	@echo "CryptoVampire2 artifact evaluation (no nix required)"
	@echo ""
	@echo "  make pull                  pull the prebuilt images from \$$REGISTRY"
	@echo "  make run                   run the full example suite -> results.csv in ./results/"
	@echo "  make test-solvers-parallel run the parallel solver matrix (quick subset by default)"
	@echo "  make shell                 drop into a shell with all tools"
	@echo "  make results               copy results out of the latest stopped container"
	@echo "  make build-nix             (authors) build+load both images with nix"
	@echo ""
	@echo "Override: REGISTRY=..., TAG=..., RESULTS_DIR=..., SOLVER_ARGS=..."

# ---------------------------------------------------------------------------
# Reviewer targets (docker only)
# ---------------------------------------------------------------------------

pull:
	@test -n "$(REGISTRY)" || (echo "Set REGISTRY to a registry prefix, see docker/README.md"; exit 1)
	docker pull $(REGISTRY)/$(IMAGE):$(TAG)
	docker pull $(REGISTRY)/$(SHELL_IMAGE):$(TAG)

# Runs the Makefile `all` target (all examples -> results/results.csv).
run:
	@mkdir -p $(RESULTS_DIR)
	docker run --rm -it $(VOLUME_ARGS) $(FULL_IMAGE)

# Runs the parallel solver matrix.  The image's default command is `make`, so
# we override it with the test-solvers-parallel target.
test-solvers-parallel:
	@mkdir -p $(RESULTS_DIR)
	docker run --rm -it $(VOLUME_ARGS) $(FULL_IMAGE) \
		make test-solvers-parallel $(SOLVER_ARGS)

# What the run/shell images really do *inside* the container.
shell:
	@mkdir -p $(RESULTS_DIR)
	docker run --rm -it $(VOLUME_ARGS) $(SHELL_IMAGE)

# Copy results out of a stopped container that was started without -v.
results:
	@id=$$(docker ps -q -l); test -n "$$id" || (echo "no container found"; exit 1); \
	docker cp $$id:$(WORKDIR)/results $(RESULTS_DIR)

# ---------------------------------------------------------------------------
# Author-only: rebuild the images from the nix flake (needs nix on the host)
# ---------------------------------------------------------------------------

build-nix:
	nix build .#docker -o result-docker
	nix build .#docker-shell -o result-docker-shell
	docker load < result-docker
	docker load < result-docker-shell
	@echo "loaded $(IMAGE):$(TAG) and $(SHELL_IMAGE):$(TAG)"
