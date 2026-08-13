
# Makefile for running cryptovampire2 tests

# 1. Get the absolute path of the current Makefile
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))

# 2. Extract just the directory portion from that path
CURRENT_DIR := $(dir $(MKFILE_PATH))

# Configuration
PROJECT_DIR := ./../..
CRATE_DIR := $(PROJECT_DIR)/crates/cryptovampire2
# As per .cargo/config.toml in the project root
# BUILD_DIR := /tmp/ccsa/build/dir/release
BUILD_DIR := $(PROJECT_DIR)/target/release
BINARY_NAME := cryptovampire
BINARY := ./$(BINARY_NAME)
RESULTS := $(CURRENT_DIR)results/results.csv
SOURCES := $(wildcard *.ptcl)
VAMPIRE_PATH :=vampire

# Ensure sequential execution
.NOTPARALLEL:

all: all-tests

.PHONY: force_cargo all-tests

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

force_cargo:
	cd $(CRATE_DIR) &&  cargo lbuild --release -p cryptovampire


# Default target
all-tests: $(BINARY) $(SOURCES)
	@for file in $(SOURCES); do \
		echo "Running test: $$file"; \
		$(BINARY) "$$file" \
			auto \
			--timeout $(if $(TIMEOUT),$(TIMEOUT),40); \
	done
