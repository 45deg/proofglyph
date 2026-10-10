ROCQ ?= rocq
OCAMLC ?= ocamlc
OCAMLFIND ?= ocamlfind
ZARITH = $(shell $(OCAMLFIND) query zarith)
BUILD := _build
FLAGS := -Q ../../proofglyph/_build Proofglyph.Language -Q . Proofglyph.Hieratic
VFILES := $(shell sed -n '/^[^[:space:]].*\.v$$/p' _CoqProject)
LIBROOT := ../../../_build/default/lib
LIBFLAGS = -I "$(ZARITH)" -I +unix -I $(LIBROOT)/core/.proofglyph_core.objs/byte -I $(LIBROOT)/proofglyph/.proofglyph_language.objs/byte -I $(LIBROOT)/hieratic/.proofglyph_hieratic.objs/byte
LIBS := zarith.cma unix.cma $(LIBROOT)/core/proofglyph_core.cma $(LIBROOT)/proofglyph/proofglyph_language.cma $(LIBROOT)/hieratic/proofglyph_hieratic.cma

.PHONY: all verify test extracted clean force print-vfiles
all: extracted

# Refresh proofglyph first; its stamp changes only when proofs are rebuilt.
../proofglyph/_build/verified: force
	$(MAKE) -C ../proofglyph verify ROCQ=$(ROCQ)

force:

verify: $(BUILD)/verified

$(BUILD)/verified: ../proofglyph/_build/verified $(VFILES) _CoqProject Makefile
	mkdir -p $(BUILD)
	cp $(VFILES) $(BUILD)/
	cd $(BUILD) && for f in $(VFILES); do \
		$(ROCQ) compile $(FLAGS) "$$f" || exit $$?; \
	done
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) Proofglyph.Hieratic.Verification Proofglyph.Hieratic.Examples Proofglyph.Hieratic.ProofglyphExamples Proofglyph.Hieratic.DesugarExamples Proofglyph.Hieratic.HieraticExamples Proofglyph.Hieratic.FileExamples
	touch $@

extracted: verify
	cd ../.. && dune build lib/hieratic/proofglyph_hieratic.cma
	cp adapter.ml main.ml test_frontend.ml ../proofglyph/persistent_hash.ml ../proofglyph/persistent_hash.mli $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -c persistent_hash.mli && $(OCAMLC) -c persistent_hash.ml
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -c frontend.mli && $(OCAMLC) -I "$(ZARITH)" -c frontend.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -c adapter.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o hieratic $(LIBS) persistent_hash.cmo frontend.cmo adapter.cmo main.ml

test: extracted
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o test_frontend $(LIBS) persistent_hash.cmo frontend.cmo adapter.cmo test_frontend.ml
	python3 test_cli.py

clean:
	rm -rf $(BUILD)

# Expose the resolved module order for the layer checks.
print-vfiles:
	@printf '%s\n' $(VFILES)
