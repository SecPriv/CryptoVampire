# Makefile for running indistinguishability tests

# Configuration
CRATE_DIR := ../..
PROJECT_DIR := $(CRATE_DIR)/../..
# As per .cargo/config.toml in the project root
BUILD_DIR := /tmp/ccsa/build/dir/release
# BUILD_DIR := $(PROJECT_DIR)/target/release
BINARY_NAME := indistinguishability
BINARY := ./$(BINARY_NAME)
RESULTS := results.csv
SOURCES := $(wildcard *.scm) $(wildcard ./stateful/*.scm)
VAMPIRE_PATH :=$(PWD)/moldvampire.sh

# 1. Get the absolute path of the current Makefile
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))

# 2. Extract just the directory portion from that path
CURRENT_DIR := $(dir $(MKFILE_PATH))

# Ensure sequential execution
.NOTPARALLEL:

# Default target
all: $(RESULTS)

# Compile the crate and update the local binary if the build artifact changed.
# We force cargo build to run every time to let it decide if recompilation is needed.
# We only touch the local binary if the new build artifact is different to avoid unnecessary test runs.
$(BINARY): force_cargo
	@if [ ! -f "$(BUILD_DIR)/$(BINARY_NAME)" ]; then \
		echo "Error: Build artifact not found at $(BUILD_DIR)/$(BINARY_NAME)"; \
		exit 1; \
	fi
	@if [ ! -f "$@" ] || ! cmp -s "$(BUILD_DIR)/$(BINARY_NAME)" "$@"; then \
		cp "$(BUILD_DIR)/$(BINARY_NAME)" "$@"; \
		echo "Updated $(BINARY)"; \
	fi

.PHONY: force_cargo
force_cargo:
	cd $(CRATE_DIR) &&  cargo lbuild --release

# Run tests to generate results.csv
# Invalidates if the binary changes or any source file changes.
$(RESULTS): $(BINARY) $(SOURCES)
	@echo "Generating $(RESULTS)..."
	@rm -f $(RESULTS)
	@for file in $(SOURCES); do \
		echo "Running test: $$file"; \
		echo "  $(BINARY) --scheme-root-directory $(CURRENT_DIR) $$file"; \
		RESULT=$(RESULTS) $(BINARY) --scheme-root-directory $(CURRENT_DIR) "$$file" || exit 1; \
	done
	@echo "Done. Results saved to $(RESULTS)"

clean:
	rm -f $(RESULTS) $(BINARY)

# Test all examples with different solver configurations (PARALLEL VERSION)
# Uses dynamic core allocation to maximize parallelism while respecting solver constraints:
#   - vampire-enabled configs: all available cores (forwarded to indistinguishability)
#   - z3-only/cvc5-only/no-solvers: 1 core each (run in parallel)
#
# Usage:
#   make test-solvers-parallel                    # Test all configs, all files
#   make test-solvers-parallel CONFIGS="..."      # Test specific configs
#   make test-solvers-parallel FILES="..."        # Test specific files
#   make test-solvers-parallel TIMEOUT=1800       # Set timeout (seconds)
#   make test-solvers-parallel CORES=8            # Set core count (default: machine cores)
#   make test-solvers-parallel RESUME=1           # Resume from checkpoint
#   make test-solvers-parallel DRY_RUN=1          # Show test plan
#
# Examples:
#   make test-solvers-parallel CONFIGS="no-vampire z3-only"
#   make test-solvers-parallel FILES="basic-hash.scm ddh-P.scm"
#   make test-solvers-parallel TIMEOUT=3600 CONFIGS="all-enabled"
#   make test-solvers-parallel CORES=8            # Use only 8 cores
#
# Environment variables:
#   SOLVER_CONFIGS - Space-separated list of configs
#   TEST_FILES - Space-separated list of files
#   TEST_TIMEOUT - Timeout in seconds (default: 1800)
#   TEST_CORES - Number of cores to use (default: machine core count)
.PHONY: test-solvers-parallel
test-solvers-parallel: $(BINARY)
	@python3 $(CURRENT_DIR)test-solvers-parallel.py \
		$(if $(CONFIGS),--configs $(CONFIGS),) \
		$(if $(FILES),--files $(FILES),) \
		$(if $(TIMEOUT),--timeout $(TIMEOUT),--timeout 1800) \
		$(if $(TEST_CORES),--cores $(TEST_CORES),) \
		$(if $(RESUME),--resume,) \
		$(if $(DRY_RUN),--dry-run,)

# Legacy sequential test script (kept for backwards compatibility)
.PHONY: test-solvers
test-solvers: $(BINARY)
	@./test-solvers.sh
