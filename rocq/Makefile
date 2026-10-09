# Each development owns its dependency on proofglyph; run these serially even with -j.
ROCQ ?= rocq
OCAMLC ?= ocamlc

.PHONY: all verify test check-layers
all: verify

verify test:
	$(MAKE) -C proofglyph $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)
	$(MAKE) -C hieratic $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)
	$(MAKE) -C calculi $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)
	$(MAKE) -C zfc $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)

check-layers:
	python3 test_layers.py

test: check-layers
