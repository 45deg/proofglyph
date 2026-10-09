ROCQ ?= rocq
BUILD := _build
FLAGS := -Q ../../proofglyph/_build Tinyprover.Proofglyph -Q . Tinyprover.Zfc

.PHONY: all verify test
all: verify

verify:
	$(MAKE) -C ../proofglyph verify ROCQ=$(ROCQ)
	mkdir -p $(BUILD)
	cd ../.. && dune exec rocq/zfc/export.exe -- rocq/zfc/prelude.ht rocq/zfc/basic.ht rocq/zfc/$(BUILD)
	cp Formula.v Axioms.v Semantics.v Deduction.v Russell.v Encoding.v Specification.v Verification.v Certificates.v $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Formula.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Axioms.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Semantics.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Deduction.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Russell.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Certificates.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Encoding.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Specification.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Verification.v
	mkdir -p $(BUILD)/deep
	cd ../.. && dune exec rocq/zfc/export.exe -- rocq/zfc/proof_prelude.ht rocq/zfc/proof_certificates.ht rocq/zfc/$(BUILD)/deep
	cp DeepVerification.v Translation.v GroundAdequacy.v Reflection.v RussellVerification.v $(BUILD)/deep/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep Tinyprover.ZfcDeep deep/Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep Tinyprover.ZfcDeep deep/DeepVerification.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep Tinyprover.ZfcDeep deep/Translation.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep Tinyprover.ZfcDeep deep/GroundAdequacy.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep Tinyprover.ZfcDeep deep/Reflection.v
	python3 russell_export.py
	cd ../.. && dune exec rocq/zfc/export.exe -- rocq/zfc/proof_prelude.ht rocq/zfc/$(BUILD)/russell/source.ht rocq/zfc/$(BUILD)/russell
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q russell Tinyprover.ZfcRussell russell/Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep Tinyprover.ZfcDeep -Q russell Tinyprover.ZfcRussell deep/RussellVerification.v
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) -Q deep Tinyprover.ZfcDeep -Q russell Tinyprover.ZfcRussell Tinyprover.Zfc.Semantics Tinyprover.Zfc.Specification Tinyprover.Zfc.Verification Tinyprover.Zfc.Certificates Tinyprover.Zfc.Russell Tinyprover.ZfcDeep.DeepVerification Tinyprover.ZfcDeep.Translation Tinyprover.ZfcDeep.GroundAdequacy Tinyprover.ZfcDeep.Reflection Tinyprover.ZfcDeep.RussellVerification

test: verify
	$(MAKE) -C ../proofglyph all ROCQ=$(ROCQ)
	cd ../.. && dune build bin/main.exe
	python3 test.py
