ROCQ ?= rocq
BUILD := _build
FLAGS := -Q ../../rocq4pa/_build Rocq4pa -Q . Zfc

.PHONY: all verify test
all: verify

verify:
	$(MAKE) -C ../rocq4pa verify ROCQ=$(ROCQ)
	mkdir -p $(BUILD)
	cd .. && dune exec zfc/export.exe -- zfc/prelude.tp zfc/basic.tp zfc/$(BUILD)
	cp Formula.v Axioms.v Semantics.v Deduction.v Encoding.v Specification.v Verification.v Certificates.v $(BUILD)/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Formula.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Axioms.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Semantics.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Deduction.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Certificates.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Encoding.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Specification.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) Verification.v
	mkdir -p $(BUILD)/deep
	cd .. && dune exec zfc/export.exe -- zfc/proof_prelude.tp zfc/proof_certificates.tp zfc/$(BUILD)/deep
	cp DeepVerification.v Translation.v GroundAdequacy.v Reflection.v $(BUILD)/deep/
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep ZfcDeep deep/Artifact.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep ZfcDeep deep/DeepVerification.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep ZfcDeep deep/Translation.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep ZfcDeep deep/GroundAdequacy.v
	cd $(BUILD) && $(ROCQ) compile $(FLAGS) -Q deep ZfcDeep deep/Reflection.v
	cd $(BUILD) && $(ROCQ) check -silent $(FLAGS) -Q deep ZfcDeep Zfc.Semantics Zfc.Specification Zfc.Verification Zfc.Certificates ZfcDeep.DeepVerification ZfcDeep.Translation ZfcDeep.GroundAdequacy ZfcDeep.Reflection

test: verify
	$(MAKE) -C ../rocq4pa all ROCQ=$(ROCQ)
	cd .. && dune build bin/main.exe
	python3 test.py
