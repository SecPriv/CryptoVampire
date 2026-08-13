OUT_DIR := ./out
PROJECT_DIR := .
BUILD_DIR := $(PROJECT_DIR)/target/release

INDISTINGUISHABILITY := $(OUT_DIR)/indistinguishability
CRYPTOVAMPIRE := $(OUT_DIR)/cryptovampire

.PHONY: cryptovampire2 cryptovampire

cryptovampire:
	cargo build --release -p cryptovampire
	cp $(BUILD_DIR)/cryptovampire $(CRYPTOVAMPIRE)

cryptovampire2:
	cargo build --release -p indistinguishability
	cp $(BUILD_DIR)/indistinguishability $(INDISTINGUISHABILITY)

doc: cryptovampire2 $(PROJECT_DIR)/crates/indistinguishability/scheme/docgen.scm
	$(INDISTINGUISHABILITY) $(PROJECT_DIR)/crates/indistinguishability/scheme/docgen.scm
	cp $(PROJECT_DIR)/docs/scheme-api.md $(OUT_DIR)