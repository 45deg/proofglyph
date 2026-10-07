# Rocq is optional for the parent project; all outputs live in _build/.
ROCQ ?= rocq
OCAMLC ?= ocamlc
BUILD := _build
VFILES := Syntax.v Substitution.v Kernel.v Program.v WellFormed.v TypingSubstitution.v Evaluation.v Confluence.v Generation.v Preservation.v Regularity.v Normalization.v Arity.v Reducibility.v TypedNormalization.v Checker.v Verification.v Extraction.v

.PHONY: all verify test clean
all: $(BUILD)/rocq4pa

$(BUILD)/verified: $(VFILES) Makefile
	@mkdir -p $(BUILD)
	cp $(VFILES) $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Syntax.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Substitution.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Kernel.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Program.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa WellFormed.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa TypingSubstitution.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Evaluation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Confluence.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Generation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Preservation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Regularity.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Normalization.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Arity.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Reducibility.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa TypedNormalization.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Checker.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Verification.v
	cd $(BUILD) && $(ROCQ) compile -Q . Rocq4pa Extraction.v
	cd $(BUILD) && $(ROCQ) check -silent -Q . Rocq4pa Rocq4pa.Verification
	touch $@

verify: $(BUILD)/verified

$(BUILD)/rocq4pa: $(BUILD)/verified main.ml
	cp main.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -w +a-4-42-70 -c checker.mli
	cd $(BUILD) && $(OCAMLC) -w +a-4-42-70 -c checker.ml
	cd $(BUILD) && $(OCAMLC) -w +a-4-42-70 -o rocq4pa checker.cmo main.ml

test: all
	python3 test_cli.py

clean:
	rm -rf $(BUILD)
