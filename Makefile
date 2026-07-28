.PHONY: build examples inspect validate validate-direct-lcnf validate-v8 validate-coverage-index bug-cards trusted-assumptions no-placeholders check beam talos-setup talos-check clean

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
	node scripts/test_wasm_validation_externals.mjs
	python3 scripts/validate_interpreters.py --plan validation-plans/native-lcnf.json
	python3 scripts/validate_interpreters.py --verify-matrix _build/validation/matrix.json

validate-direct-lcnf:
	python3 scripts/validate_interpreters.py \
		--plan validation-plans/direct-lcnf.json \
		--out-dir _build/validation-direct-lcnf
	python3 scripts/validate_interpreters.py \
		--verify-matrix _build/validation-direct-lcnf/matrix.json

validate-v8:
	python3 scripts/validate_interpreters.py \
		--plan validation-plans/native-lcnf-v8-scalars.json \
		--out-dir _build/validation-v8
	python3 scripts/validate_interpreters.py \
		--verify-matrix _build/validation-v8/matrix.json

validate-coverage-index: validate validate-direct-lcnf validate-v8
	python3 scripts/validation_coverage_index.py \
		--plan validation-plans/coverage-index.json \
		--out _build/validation-coverage/index.json
	python3 scripts/validation_coverage_index.py \
		--verify-index _build/validation-coverage/index.json

no-placeholders:
	@if rg -n "sorry|admit" Fir docs Inspect FirValidation*.lean; then \
		echo "Found proof placeholders"; \
		exit 1; \
	fi

bug-cards:
	python3 scripts/validate_bug_cards.py

trusted-assumptions:
	python3 scripts/validate_trusted_assumptions.py

check: build examples validate-coverage-index bug-cards trusted-assumptions no-placeholders

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
	lean-beam sync Fir/Validation/DirectLCNF.lean
	lean-beam sync Fir/Validation.lean
	lean-beam sync FirValidationNative.lean
	lean-beam sync FirValidationLCNF.lean
	lean-beam sync FirValidationDirectNative.lean
	lean-beam sync FirValidationDirectLCNF.lean
	lean-beam sync FirValidationWasm.lean
	lean-beam sync Fir/Wasm/Examples.lean
	lean-beam sync Inspect

talos-setup:
	bash scripts/setup-talos.sh
	lake -d integration/talos update

talos-check:
	lake -d integration/talos build

clean:
	lake clean
