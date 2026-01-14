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
SOURCES := $(wildcard *.scm)

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
	cd $(CRATE_DIR) && cargo build --release

# Run tests to generate results.csv
# Invalidates if the binary changes or any source file changes.
$(RESULTS): $(BINARY) $(SOURCES)
	@echo "Generating $(RESULTS)..."
	@rm -f $(RESULTS)
	@for file in $(SOURCES); do \
		echo "Running test: $$file"; \
		RESULT=$(RESULTS) $(BINARY) file "$$file" || exit 1; \
	done
	@echo "Done. Results saved to $(RESULTS)"

clean:
	rm -f $(RESULTS) $(BINARY)
