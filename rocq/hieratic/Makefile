ROCQ ?= rocq
OCAMLC ?= ocamlc
OCAMLFIND ?= ocamlfind
ZARITH = $(shell $(OCAMLFIND) query zarith)
BUILD := _build
FLAGS := -Q ../../proofglyph/_build Tinyprover.Proofglyph -Q . Tinyprover.Hieratic
VFILES := $(shell sed -n '/^[^[:space:]].*\.v$$/p' _CoqProject)
LIBROOT := ../../../_build/default/lib
LIBFLAGS = -I "$(ZARITH)" -I +unix -I $(LIBROOT)/core/.tinyprover_core.objs/byte -I $(LIBROOT)/proofglyph/.tinyprover_proofglyph.objs/byte -I $(LIBROOT)/hieratic/.tinyprover_hieratic.objs/byte
LIBS := zarith.cma unix.cma $(LIBROOT)/core/tinyprover_core.cma $(LIBROOT)/proofglyph/tinyprover_proofglyph.cma $(LIBROOT)/hieratic/tinyprover_hieratic.cma

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
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) Tinyprover.Hieratic.Verification Tinyprover.Hieratic.Examples Tinyprover.Hieratic.ProofglyphExamples Tinyprover.Hieratic.DesugarExamples Tinyprover.Hieratic.HieraticExamples Tinyprover.Hieratic.FileExamples
	touch $@

extracted: verify
	cd ../.. && dune build lib/hieratic/tinyprover_hieratic.cma
	cp adapter.ml main.ml test_frontend.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -c frontend.mli && $(OCAMLC) -I "$(ZARITH)" -c frontend.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -c adapter.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o hieratic $(LIBS) frontend.cmo adapter.cmo main.ml

test: extracted
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o test_frontend $(LIBS) frontend.cmo adapter.cmo test_frontend.ml
	python3 test_cli.py

clean:
	rm -rf $(BUILD)

# Expose the resolved module order for the layer checks.
print-vfiles:
	@printf '%s\n' $(VFILES)
