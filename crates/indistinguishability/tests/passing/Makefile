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
		echo "  $(BINARY) --root-directory $(CURRENT_DIR) file $$file"; \
		RESULT=$(RESULTS) $(BINARY) --root-directory $(CURRENT_DIR) file "$$file" || exit 1; \
	done
	@echo "Done. Results saved to $(RESULTS)"

clean:
	rm -f $(RESULTS) $(BINARY)

# Test all examples with different solver configurations
# Usage: make test-solvers [CONFIG=all-enabled|no-vampire|no-z3|no-cvc5|vampire-only|z3-only|cvc5-only|no-solvers]
# If CONFIG is not specified, tests all configurations
.PHONY: test-solvers
test-solvers: $(BINARY)
	@./test-solvers.sh
