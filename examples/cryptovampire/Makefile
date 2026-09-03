
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
#
# Per-file extra flags (models that need them):
#   *-execpred.ptcl          -> --exec-pred --pairwise-find-fa -l
#   *-add-rewrite*.ptcl and
#   feldhofer-ind*.ptcl      -> --pairwise-find-fa -l
#   everything else          -> plain auto
#
# `lak-tag-add-rewrite.ptcl` is the faithful base rendering (true query, no
# bridge lemma) and is not provable as-is; it is skipped here in favour of its
# provable -plain / -named-exec / -execpred variants.
#
# Each test gets up to 2 attempts (the solver suite is occasionally flaky);
# a test that still fails makes this target fail.
TEST_TIMEOUT := $(if $(TIMEOUT),$(TIMEOUT),40)

all-tests: $(BINARY) $(SOURCES)
	@for file in $(SOURCES); do \
		BEFORE=""; AFTER=""; \
		case "$$file" in \
			*-execpred.ptcl) \
				BEFORE="--exec-pred --pairwise-find-fa"; AFTER="-l";; \
			lak-tag-add-rewrite.ptcl) \
				echo "SKIP $$file (base lak-tag add-rewrite is not provable as-is; see the -plain/-named-exec/-execpred variants)"; \
				continue;; \
			*-add-rewrite*.ptcl|feldhofer-ind*.ptcl) \
				BEFORE="--pairwise-find-fa"; AFTER="-l";; \
		esac; \
		echo "Running test: $$file $$BEFORE auto $$AFTER"; \
		attempt=1; \
		until $(BINARY) "$$file" $$BEFORE auto $$AFTER --timeout $(TEST_TIMEOUT); do \
			attempt=$$((attempt+1)); \
			if [ $$attempt -gt 2 ]; then \
				echo "TEST FAILED: $$file"; \
				exit 1; \
			fi; \
			echo "  ...retrying $$file (attempt $$attempt/2)..."; \
		done; \
	done
