# Makefile for the cryptovampire (v1, .ptcl) corpus.
#
# How it works (make-like):
#   * Each model declares its flags in a first-line pragma, resolved by
#     ./flags.sh -- see that file for the token grammar. `-l` is always on.
#   * For every runnable model we keep a stamp results/<name>.ok (gitignored),
#     touched only on success. A stamp older than its .ptcl or than the rebuilt
#     binary makes make rerun that model; failed models leave no stamp and are
#     rerun on the next `make`. `make clean` drops all stamps.
#   * No retries: one run per model, make stops at the first failure.
# .NOTPARALLEL by design: running 20+ solvers concurrently just thrashes.

MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
CURRENT_DIR := $(dir $(MKFILE_PATH))

PROJECT_DIR := ./../..
CRATE_DIR   := $(PROJECT_DIR)/crates/cryptovampire
BUILD_DIR   := $(PROJECT_DIR)/target/release
BINARY_NAME := cryptovampire
BINARY      := ./$(BINARY_NAME)

.NOTPARALLEL:

# Models whose pragma says `skip` are excluded from the run entirely.
PTCL     := $(wildcard *.ptcl)
SKIPPED  := $(shell for f in $(PTCL); do [ "$$(./flags.sh "$$f")" = "SKIP" ] && echo "$$f"; done)
RUNNABLE := $(filter-out $(SKIPPED),$(PTCL))
STAMPS   := $(patsubst %.ptcl,results/%.ok,$(RUNNABLE))

.PHONY: all clean force_cargo

all: $(STAMPS)
	@echo "OK: $(words $(STAMPS))/$(words $(PTCL)) models pass (skipped: $(words $(SKIPPED)))."

clean:
	@rm -rf results

# Compile the crate and update the local binary if the build artifact changed.
# We force the build to run every time so cargo decides if recompilation is
# needed, and only re-copy the binary when the artifact differs (otherwise all
# stamps would go stale on every `make`).
$(BINARY): force_cargo
	@if [ ! -f "$(BUILD_DIR)/$(BINARY_NAME)" ]; then \
		echo "Error: build artifact not found at $(BUILD_DIR)/$(BINARY_NAME)"; \
		exit 1; \
	fi
	@if [ ! -f "$@" ] || ! cmp -s "$(BUILD_DIR)/$(BINARY_NAME)" "$@"; then \
		cp "$(BUILD_DIR)/$(BINARY_NAME)" "$@"; \
		echo "Updated $(BINARY)"; \
	fi

force_cargo:
	cd $(CRATE_DIR) && cargo build --release -p cryptovampire

results:
	@mkdir -p results

results/%.ok: %.ptcl $(BINARY) | results
	@echo "TEST  $<  flags:[$$(TIMEOUT="$(TIMEOUT)" ./flags.sh "$<")]"; \
	$(BINARY) "$<" $$(TIMEOUT="$(TIMEOUT)" ./flags.sh "$<") && touch "$@"
