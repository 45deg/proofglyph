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
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Syntax.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Substitution.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Kernel.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Program.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa WellFormed.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa TypingSubstitution.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Evaluation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Confluence.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Generation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Preservation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Regularity.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Normalization.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Arity.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Reducibility.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa TypedNormalization.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Checker.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Verification.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Extraction.v
	cd $(BUILD) && $(ROCQ) check -silent -Q . Tinyprover.Pa Tinyprover.Pa.Verification
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
