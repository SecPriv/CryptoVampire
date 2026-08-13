OUT_DIR := ./out
PROJECT_DIR := .
BUILD_DIR := $(PROJECT_DIR)/target/release

CRYPTOVAMPIRE2 := $(OUT_DIR)/cryptovampire2
CRYPTOVAMPIRE := $(OUT_DIR)/cryptovampire

BOOK_DIR := $(PROJECT_DIR)/docs

.PHONY: cryptovampire2 cryptovampire doc html

cryptovampire:
	cargo build --release -p cryptovampire
	cp $(BUILD_DIR)/cryptovampire $(CRYPTOVAMPIRE)

cryptovampire2:
	mkdir -p $(OUT_DIR)
	cargo build --release -p cryptovampire2
	cp $(BUILD_DIR)/cryptovampire2 $(CRYPTOVAMPIRE2)

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
