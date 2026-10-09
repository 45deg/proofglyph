ROCQ ?= rocq
BUILD := _build
FLAGS := -Q ../../proofglyph/_build Tinyprover.Proofglyph -Q . Tinyprover.Calculi

.PHONY: all export verify test
all: test

export:
	mkdir -p $(BUILD)
	cd ../.. && dune exec rocq/calculi/export.exe -- rocq/calculi/$(BUILD)

verify: export
	$(MAKE) -C ../proofglyph verify ROCQ=$(ROCQ)
	cp Calculi.v Encoding.v Verification.v Derivations.v CutElimination.v Restoration.v Examples.v $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Calculi.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Encoding.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) NKArtifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) LKArtifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Verification.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Derivations.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) CutElimination.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Restoration.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Examples.v
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) Tinyprover.Calculi.Calculi Tinyprover.Calculi.Encoding Tinyprover.Calculi.Verification Tinyprover.Calculi.Derivations Tinyprover.Calculi.CutElimination Tinyprover.Calculi.Restoration Tinyprover.Calculi.Examples

test: verify
	$(MAKE) -C ../proofglyph all ROCQ=$(ROCQ)
	cd ../.. && dune build bin/main.exe
	python3 test.py
