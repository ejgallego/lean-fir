.PHONY: build examples inspect validate validate-v8 bug-cards trusted-assumptions no-placeholders check beam talos-setup talos-check clean

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
	python3 scripts/validate_interpreters.py --plan validation-plans/native-lcnf.json
	python3 scripts/validate_interpreters.py --verify-matrix _build/validation/matrix.json

validate-v8:
	python3 scripts/validate_interpreters.py \
		--case boxed-uint32 --case packed-project-usize \
		--case direct-call --case captured-partial --case capture-17-list \
		--case recursive-empty --case recursive-traversal --case nat-add-small \
		--case uint8-max --case uint16-max --case uint32-max \
		--case uint64-max --case usize-max \
		--case uint8-roundtrip --case uint16-roundtrip \
		--case uint32-roundtrip --case uint64-roundtrip --case usize-roundtrip \
		--case nat-list-nonempty --case nat-list-nonempty-bool \
		--case nat-list-empty-bool --case unicode-string-roundtrip \
		--case int-positive-roundtrip --case int-negative-roundtrip \
		--case int-immediate-max --case int-immediate-min \
		--case int-heap-positive-boundary --case int-heap-negative-boundary \
		--case byte-array-roundtrip --case byte-array-size \
		--case byte-array-get-zero --case byte-array-get-high-bit \
		--case byte-array-get-max \
		--case byte-array-set-unique --case byte-array-set-shared \
		--plan validation-plans/native-v8-scalars.json \
		--out-dir _build/validation-v8
	python3 scripts/validate_interpreters.py \
		--verify-matrix _build/validation-v8/matrix.json

no-placeholders:
	@if rg -n "sorry|admit" Fir docs Inspect FirValidation*.lean; then \
		echo "Found proof placeholders"; \
		exit 1; \
	fi

bug-cards:
	python3 scripts/validate_bug_cards.py

trusted-assumptions:
	python3 scripts/validate_trusted_assumptions.py

check: build examples validate validate-v8 bug-cards trusted-assumptions no-placeholders

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
