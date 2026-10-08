ROCQ ?= rocq
BUILD := _build
FLAGS := -Q ../../rocq4pa/_build Rocq4pa -Q . Calculi

.PHONY: all export verify test
all: test

export:
	mkdir -p $(BUILD)
	cd .. && dune exec calculi/export.exe -- calculi/$(BUILD)

verify: export
	$(MAKE) -C ../rocq4pa verify ROCQ=$(ROCQ)
	cp Calculi.v Encoding.v Verification.v $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Calculi.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Encoding.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Verification.v
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) Calculi.Calculi Calculi.Encoding Calculi.Verification

test: verify
	$(MAKE) -C ../rocq4pa all ROCQ=$(ROCQ)
	cd .. && dune build bin/main.exe
	python3 test.py
