# Each development owns its dependency on pa; run these serially even with -j.
ROCQ ?= rocq
OCAMLC ?= ocamlc

.PHONY: all verify test check-layers
all: verify

verify test:
	$(MAKE) -C pa $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)
	$(MAKE) -C tp $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)
	$(MAKE) -C calculi $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)
	$(MAKE) -C zfc $@ ROCQ=$(ROCQ) OCAMLC=$(OCAMLC)

check-layers:
	python3 test_layers.py

test: check-layers
