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
FIR_CHECK_JOBS ?= 8
export FIR_CHECK_JOBS

# Keep only the current failed run for diagnosis. Opt in to keeping successful
# scratch for a specific investigation; CI logs are the durable run record.
FIR_KEEP_VALIDATION ?= 0
FIR_VERBOSE ?= 0
FIR_TOOL_LOG_DIR ?= $(CURDIR)/.deps/tool-logs
export FIR_VERBOSE FIR_TOOL_LOG_DIR

.PHONY: help build examples scalar-surface-check inspect validate-harness validate validate-direct-lcnf validate-v8 validate-source-from-v8 validate-native-oracle-attestations validate-coverage-index bug-cards trusted-assumptions proof-trust-sources proof-trust-tests proof-trust no-placeholders mailbox-check mailbox-list mailbox-deliver mailbox-test tooling-unit-check tooling-check check beam talos-setup talos-check clean

help:
	@printf '%s\n' 'FIR commands are concise by default; use FIR_VERBOSE=1 for live tool output.' \
		'  make check              full repository gate' \
		'  make talos-check        Talos proof gate (after talos-setup)' \
		'  make mailbox-list       actionable coordination threads' \
		'  scripts/mailbox brief ID  compact event review'

build:
	@bash scripts/quiet-run.sh build -- lake build

examples:
	@bash scripts/quiet-run.sh examples -- lake build Fir.LeanIR.LegacyExamples Fir.LeanIR.HygieneExamples \
		Fir.LeanIR.InterpreterExamples \
		Fir.LeanIR.Passes.SimpCaseExamples Fir.Wasm.Examples \
		Fir.Wasm.Emit.Examples

scalar-surface-check:
	@bash scripts/quiet-run.sh scalar-surface-build -- lake exe fir-wasm-scalar-surface _build/wasm-scalar-surface.wasm
	@bash scripts/quiet-run.sh scalar-surface-check -- node scripts/test_wasm_scalar_surface.mjs _build/wasm-scalar-surface.wasm

inspect:
	@bash scripts/quiet-run.sh inspect -- lake lean Inspect

validate-harness:
	@bash scripts/quiet-run.sh validate-clean -- python3 scripts/test_clean_validation.py
	@bash scripts/quiet-run.sh validate-interpreters-test -- python3 scripts/test_validate_interpreters.py
	@bash scripts/quiet-run.sh validate-reuse-test -- python3 scripts/test_validation_reuse.py
	@bash scripts/quiet-run.sh talos-attestation-test -- python3 scripts/test_talos_build_attestation.py
	@bash scripts/quiet-run.sh validation-parallel-test -- python3 scripts/test_validation_parallel.py
	@bash scripts/quiet-run.sh float-transport-test -- node scripts/test_wasm_bit_exact_float_transport.mjs
	@bash scripts/quiet-run.sh wasm-externals-test -- node scripts/test_wasm_validation_externals.mjs

validate: validate-harness
	@bash scripts/quiet-run.sh validate-native-lcnf -- python3 scripts/validate_interpreters.py --plan validation-plans/native-lcnf.json
	@bash scripts/quiet-run.sh validate-native-lcnf-receipt -- python3 scripts/validate_interpreters.py --verify-matrix _build/validation/matrix.json

validate-direct-lcnf:
	@bash scripts/quiet-run.sh validate-direct-lcnf -- python3 scripts/validate_interpreters.py \
		--plan validation-plans/direct-lcnf.json \
		--out-dir _build/validation-direct-lcnf
	@bash scripts/quiet-run.sh validate-direct-lcnf-receipt -- python3 scripts/validate_interpreters.py \
		--verify-matrix _build/validation-direct-lcnf/matrix.json

validate-v8:
	@bash scripts/quiet-run.sh validate-v8 -- python3 scripts/validate_interpreters.py \
		--plan validation-plans/native-lcnf-v8-scalars.json \
		--out-dir _build/validation-v8
	@bash scripts/quiet-run.sh validate-v8-receipt -- python3 scripts/validate_interpreters.py \
		--verify-matrix _build/validation-v8/matrix.json

validate-source-from-v8: validate-v8
	@bash scripts/quiet-run.sh validate-source-reuse -- python3 scripts/verify_validation_reuse.py \
		--receipt _build/validation-v8/evidence-receipt.json \
		--plan validation-plans/native-lcnf.json

validate-native-oracle-attestations: validate-v8
	@bash scripts/quiet-run.sh oracle-attestations -- python3 scripts/record_backend_comparisons.py \
		--evidence-receipt _build/validation-v8/evidence-receipt.json \
		--policy validation-plans/native-oracle-attestations.json
	@bash scripts/quiet-run.sh oracle-attestations-receipt -- python3 scripts/record_backend_comparisons.py \
		--verify-attestations \
		_build/validation-comparison-attestations/attestations.json \
		--policy validation-plans/native-oracle-attestations.json

validate-coverage-index: validate-harness validate-source-from-v8 validate-direct-lcnf validate-native-oracle-attestations
	@bash scripts/quiet-run.sh validation-coverage-index -- python3 scripts/validation_coverage_index.py \
		--plan validation-plans/coverage-index.json \
		--out _build/validation-coverage/index.json
	@bash scripts/quiet-run.sh validation-coverage-receipt -- python3 scripts/validation_coverage_index.py \
		--verify-index _build/validation-coverage/index.json

no-placeholders:
	@if rg -n -w "sorry|admit" Fir docs Inspect FirValidation*.lean; then \
		echo "Found proof placeholders"; \
		exit 1; \
	fi

bug-cards:
	@bash scripts/quiet-run.sh bug-cards -- python3 scripts/validate_bug_cards.py

trusted-assumptions:
	@if grep -qx 'leanprover/lean4:v4.34.0-rc2' lean-toolchain; then \
		bash scripts/quiet-run.sh trusted-assumptions -- python3 scripts/validate_trusted_assumptions.py \
			--profile lean-4.34-rc2 --lean-project "$(CURDIR)"; \
	else \
		bash scripts/quiet-run.sh trusted-assumptions -- python3 scripts/validate_trusted_assumptions.py; \
	fi

proof-trust-sources:
	@bash scripts/quiet-run.sh proof-trust-sources -- python3 integration/talos/check-proof-trust.py --sources-only

proof-trust-tests:
	@bash scripts/quiet-run.sh proof-trust-tests -- python3 integration/talos/test_proof_trust.py

# Requires talos-setup; forces elaboration of the exact compiled inventories.
proof-trust:
	@bash scripts/quiet-run.sh proof-trust -- python3 integration/talos/check-proof-trust.py

mailbox-check:
	@scripts/mailbox check

mailbox-list:
	@scripts/mailbox list

mailbox-deliver:
	@test -n "$(DRAFT)" || { echo "usage: make mailbox-deliver DRAFT=/path/to/message.md [NOTIFY_SESSION=session]"; exit 2; }
	@scripts/mailbox deliver "$(DRAFT)" $(if $(NOTIFY_SESSION),--notify-session "$(NOTIFY_SESSION)")

mailbox-test:
	@bash scripts/quiet-run.sh mailbox-test -- node --test scripts/mailbox.test.mjs

tooling-unit-check:
	@$(MAKE) --no-print-directory -C tooling unit-check

tooling-check:
	@$(MAKE) --no-print-directory -C tooling check FIR_BINARYEN_DIR="$(FIR_BINARYEN_DIR)"

.PHONY: clean-validation check-run

clean-validation:
	@bash scripts/quiet-run.sh clean-validation -- python3 scripts/clean_validation.py

check:
	@$(MAKE) --no-print-directory clean-validation
	@$(MAKE) --no-print-directory check-run
	@if test "$(FIR_KEEP_VALIDATION)" != 1; then $(MAKE) --no-print-directory clean-validation; fi

# Internal gate graph: consumers finish verifying the same run before cleanup.
check-run: tooling-unit-check build examples scalar-surface-check validate-coverage-index bug-cards trusted-assumptions proof-trust-sources proof-trust-tests no-placeholders mailbox-test

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
	@bash scripts/quiet-run.sh talos-setup -- bash tooling/talos-434/setup.sh

talos-check:
	@bash scripts/quiet-run.sh talos-check -- bash tooling/talos-434/check.sh

clean:
	@bash scripts/quiet-run.sh clean -- lake clean
