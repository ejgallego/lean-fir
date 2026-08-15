ifeq ($(origin LAKE_CACHE_DIR), undefined)
LAKE_CACHE_DIR := $(shell bash scripts/fir-lake-cache-path.sh)
ifeq ($(strip $(LAKE_CACHE_DIR)),)
$(error failed to initialize FIR's Lake artifact cache)
endif
endif
LAKE_ARTIFACT_CACHE ?= true
LAKE_RESTORE_ARTIFACTS ?= true
export LAKE_CACHE_DIR LAKE_ARTIFACT_CACHE LAKE_RESTORE_ARTIFACTS

FIR_BINARYEN_DIR ?= $(CURDIR)/.deps/lcnf-c-wasm/emsdk/upstream/bin

.PHONY: build examples scalar-surface-check inspect validate validate-direct-lcnf validate-v8 validate-native-oracle-attestations validate-coverage-index bug-cards trusted-assumptions no-placeholders mailbox-check mailbox-list mailbox-test tooling-unit-check tooling-check check beam talos-setup talos-check clean

build:
	lake build

examples:
	lake build Fir.LeanIR.LegacyExamples Fir.LeanIR.HygieneExamples \
		Fir.LeanIR.InterpreterExamples \
		Fir.LeanIR.Passes.SimpCaseExamples Fir.Wasm.Examples \
		Fir.Wasm.Emit.Examples

scalar-surface-check:
	lake exe fir-wasm-scalar-surface _build/wasm-scalar-surface.wasm
	node scripts/test_wasm_scalar_surface.mjs _build/wasm-scalar-surface.wasm

inspect:
	lake lean Inspect

validate:
	python3 scripts/test_validate_interpreters.py
	node scripts/test_wasm_bit_exact_float_transport.mjs
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

validate-native-oracle-attestations: validate-v8
	python3 scripts/record_backend_comparisons.py \
		--evidence-receipt _build/validation-v8/evidence-receipt.json \
		--policy validation-plans/native-oracle-attestations.json
	python3 scripts/record_backend_comparisons.py \
		--verify-attestations \
		_build/validation-comparison-attestations/attestations.json \
		--policy validation-plans/native-oracle-attestations.json

validate-coverage-index: validate validate-direct-lcnf validate-native-oracle-attestations
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

mailbox-check:
	node scripts/mailbox.mjs check

mailbox-list:
	node scripts/mailbox.mjs list

mailbox-test:
	node --test scripts/mailbox.test.mjs

tooling-unit-check:
	$(MAKE) -C tooling unit-check

tooling-check:
	$(MAKE) -C tooling check FIR_BINARYEN_DIR="$(FIR_BINARYEN_DIR)"

check: tooling-unit-check build examples scalar-surface-check validate-coverage-index bug-cards trusted-assumptions no-placeholders mailbox-test

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
