.PHONY: build examples inspect validate bug-cards no-placeholders check beam talos-setup talos-check clean

build:
	lake build

examples:
	lake build Fir.LeanIR.LegacyExamples Fir.LeanIR.HygieneExamples \
		Fir.LeanIR.InterpreterExamples \
		Fir.LeanIR.Passes.SimpCaseExamples Fir.Wasm.Examples

inspect:
	lake lean Inspect

validate:
	python3 scripts/test_validate_interpreters.py
	python3 scripts/validate_interpreters.py

no-placeholders:
	@if rg -n "sorry|admit" Fir docs Inspect FirValidation*.lean; then \
		echo "Found proof placeholders"; \
		exit 1; \
	fi

bug-cards:
	python3 scripts/validate_bug_cards.py

check: build examples validate bug-cards no-placeholders

beam:
	lean-beam sync Fir/LeanIR.lean
	lean-beam sync Fir/Wasm.lean
	lean-beam sync Fir.lean
	lean-beam sync Fir/LeanIR/LegacyExamples.lean
	lean-beam sync Fir/LeanIR/HygieneExamples.lean
	lean-beam sync Fir/LeanIR/InterpreterExamples.lean
	lean-beam sync Fir/Validation/Protocol.lean
	lean-beam sync Fir/Validation/Corpus.lean
	lean-beam sync Fir/Validation/LCNF.lean
	lean-beam sync Fir/Validation.lean
	lean-beam sync FirValidationNative.lean
	lean-beam sync FirValidationLCNF.lean
	lean-beam sync Fir/Wasm/Examples.lean
	lean-beam sync Inspect

talos-setup:
	bash scripts/setup-talos.sh
	lake -d integration/talos update

talos-check:
	lake -d integration/talos build

clean:
	lake clean
