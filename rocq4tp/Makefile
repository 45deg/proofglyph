ROCQ ?= rocq
OCAMLC ?= ocamlc
BUILD := _build
FLAGS := -Q ../../rocq4pa/_build Rocq4pa -Q . Rocq4tp
VFILES := Surface.v Resolve.v Compile.v PaCodec.v PaCompile.v Examples.v PaExamples.v Verification.v Extraction.v
LIBROOT := ../../_build/default/lib
LIBFLAGS := -I +unix -I $(LIBROOT)/core/.tinyprover_core.objs/byte -I $(LIBROOT)/pa/.tinyprover_pa.objs/byte -I $(LIBROOT)/tp/.tinyprover_tp.objs/byte
LIBS := unix.cma $(LIBROOT)/core/tinyprover_core.cma $(LIBROOT)/pa/tinyprover_pa.cma $(LIBROOT)/tp/tinyprover_tp.cma

.PHONY: all verify test extracted
all: extracted

verify:
	$(MAKE) -C ../rocq4pa verify ROCQ=$(ROCQ)
	mkdir -p $(BUILD)
	cp $(VFILES) $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Surface.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Resolve.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Compile.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) PaCodec.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) PaCompile.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Examples.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) PaExamples.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Verification.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Extraction.v
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) Rocq4tp.Verification Rocq4tp.Examples Rocq4tp.PaExamples

extracted: verify
	cd .. && dune build lib/tp/tinyprover_tp.cma
	cp adapter.ml main.ml test_frontend.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -c frontend.mli && $(OCAMLC) -c frontend.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -c adapter.ml
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o rocq4tp $(LIBS) frontend.cmo adapter.cmo main.ml

test: extracted
	cd $(BUILD) && $(OCAMLC) $(LIBFLAGS) -o test_frontend $(LIBS) frontend.cmo adapter.cmo test_frontend.ml
	python3 test_cli.py
