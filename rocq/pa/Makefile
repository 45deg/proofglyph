# Rocq is optional for the parent project; all outputs live in _build/.
ROCQ ?= rocq
OCAMLC ?= ocamlc
BUILD := _build
VFILES := Syntax.v Substitution.v KernelImpl.v Kernel.v Program.v WellFormed.v TypingSubstitution.v EvaluationSpec.v Evaluation.v Confluence.v ConfluenceCorrectness.v Generation.v Preservation.v PreservationCorrectness.v Regularity.v Normalization.v Arity.v Reducibility.v TypedNormalization.v CheckerSpec.v CheckerImpl.v Checker.v CodecSpec.v CodecImpl.v CodecCorrectness.v Codec.v Verification.v Extraction.v

.PHONY: all verify test clean
all: $(BUILD)/pa

$(BUILD)/verified: $(VFILES) Makefile
	@mkdir -p $(BUILD)
	cp $(VFILES) $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Syntax.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Substitution.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa KernelImpl.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Kernel.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Program.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa WellFormed.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa TypingSubstitution.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa EvaluationSpec.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Evaluation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Confluence.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa ConfluenceCorrectness.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Generation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Preservation.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa PreservationCorrectness.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Regularity.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Normalization.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Arity.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Reducibility.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa TypedNormalization.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa CheckerSpec.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa CheckerImpl.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Checker.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa CodecSpec.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa CodecImpl.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa CodecCorrectness.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Codec.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Verification.v
	cd $(BUILD) && $(ROCQ) compile -Q . Tinyprover.Pa Extraction.v
	cd $(BUILD) && $(ROCQ) check -silent -Q . Tinyprover.Pa Tinyprover.Pa.Verification
	touch $@

verify: $(BUILD)/verified

$(BUILD)/pa: $(BUILD)/verified main.ml
	cp main.ml $(BUILD)/
	cd $(BUILD) && $(OCAMLC) -w +a-4-42-70 -c checker.mli
	cd $(BUILD) && $(OCAMLC) -w +a-4-42-70 -c checker.ml
	cd $(BUILD) && $(OCAMLC) -w +a-4-42-70 -o pa checker.cmo main.ml

test: all
	python3 test_cli.py

clean:
	rm -rf $(BUILD)
