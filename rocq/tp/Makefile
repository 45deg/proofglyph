ROCQ ?= rocq
OCAMLC ?= ocamlc
OCAMLFIND ?= ocamlfind
ZARITH = $(shell $(OCAMLFIND) query zarith)
BUILD := _build
FLAGS := -Q ../../pa/_build Tinyprover.Pa -Q . Tinyprover.Tp
VFILES := $(shell sed -n '/^[^[:space:]].*\.v$$/p' _CoqProject)
LIBROOT := ../../../_build/default/lib
LIBFLAGS = -I "$(ZARITH)" -I +unix -I $(LIBROOT)/core/.tinyprover_core.objs/byte -I $(LIBROOT)/pa/.tinyprover_pa.objs/byte -I $(LIBROOT)/tp/.tinyprover_tp.objs/byte
LIBS := zarith.cma unix.cma $(LIBROOT)/core/tinyprover_core.cma $(LIBROOT)/pa/tinyprover_pa.cma $(LIBROOT)/tp/tinyprover_tp.cma

.PHONY: all verify test extracted clean force print-vfiles
all: extracted

# Refresh pa first; its stamp changes only when proofs are rebuilt.
../pa/_build/verified: force
	$(MAKE) -C ../pa verify ROCQ=$(ROCQ)

force:

verify: $(BUILD)/verified

$(BUILD)/verified: ../pa/_build/verified $(VFILES) _CoqProject Makefile
	mkdir -p $(BUILD)
	cp $(VFILES) $(BUILD)/
	cd $(BUILD) && for f in $(VFILES); do \
		$(ROCQ) compile $(FLAGS) "$$f" || exit $$?; \
	done
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) Tinyprover.Tp.Verification Tinyprover.Tp.Examples Tinyprover.Tp.PaExamples Tinyprover.Tp.DesugarExamples Tinyprover.Tp.TpExamples Tinyprover.Tp.FileExamples
	touch $@

extracted: verify
	cd ../.. && dune build lib/tp/tinyprover_tp.cma
	cp adapter.ml main.ml test_frontend.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -I "$(ZARITH)" -c frontend.mli && $(OCAMLC) -I "$(ZARITH)" -c frontend.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -c adapter.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o tp $(LIBS) frontend.cmo adapter.cmo main.ml

test: extracted
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o test_frontend $(LIBS) frontend.cmo adapter.cmo test_frontend.ml
	python3 test_cli.py

clean:
	rm -rf $(BUILD)

# Expose the resolved module order for the layer checks.
print-vfiles:
	@printf '%s\n' $(VFILES)
