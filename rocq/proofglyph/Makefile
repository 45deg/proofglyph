# Rocq is optional for the parent project; all outputs live in _build/.
ROCQ ?= rocq
OCAMLC ?= ocamlc
OCAMLFIND ?= ocamlfind
ZARITH = $(shell $(OCAMLFIND) query zarith)
BUILD := _build
VFILES := $(shell sed -n '/^[^[:space:]].*\.v$$/p' _CoqProject)

.PHONY: all verify test clean print-vfiles
all: $(BUILD)/proofglyph

$(BUILD)/verified: $(VFILES) _CoqProject Makefile
	@mkdir -p $(BUILD)
	cp $(VFILES) $(BUILD)/
	cd $(BUILD) && for f in $(VFILES); do \
		$(ROCQ) compile -Q . Proofglyph.Language "$$f" || exit $$?; \
	done
	cd $(BUILD) && $(ROCQ) check -silent -Q . Proofglyph.Language Proofglyph.Language.Verification
	touch $@

verify: $(BUILD)/verified

$(BUILD)/proofglyph: $(BUILD)/verified main.ml persistent_hash.ml persistent_hash.mli
	cp main.ml persistent_hash.ml persistent_hash.mli $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -c persistent_hash.mli && $(OCAMLC) -c persistent_hash.ml
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -w +a-4-42-70 -c checker.mli
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -w +a-4-42-70 -c checker.ml
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -w +a-4-42-70 -o proofglyph zarith.cma persistent_hash.cmo checker.cmo main.ml

test: all
	cp test_cache.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -c cache_reference.mli && $(OCAMLC) -I "$(ZARITH)" -c cache_reference.ml
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -o test_cache zarith.cma persistent_hash.cmo checker.cmo cache_reference.cmo test_cache.ml
	$(BUILD)/test_cache
	python3 test_cli.py

clean:
	rm -rf $(BUILD)

# Expose the resolved module order for the layer checks.
print-vfiles:
	@printf '%s\n' $(VFILES)
