TOOLING_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(TOOLING_DIR)/..)
ARRAY_PROBE_DIR := $(TOOLING_DIR)/array-probe
FIR_BINARYEN_DIR ?= $(REPO_ROOT)/.deps/lcnf-c-wasm/emsdk/upstream/bin
FIR_TOOLING_TMPDIR ?= $(REPO_ROOT)/.deps/tooling-tmp
FIR_LAKE_CACHE_DIR ?= $(shell bash "$(REPO_ROOT)/scripts/fir-lake-cache-path.sh")
BINARYEN_REVISION := version 128 (version_127-18-g2eb472cd6)

.PHONY: no-skips unit-check binaryen-check wasm-check profile-check array-probe-check check

no-skips:
	@if rg -n 'test[.]skip|skip[[:space:]]*:' "$(TOOLING_DIR)" \
		--glob '*.test.mjs'; then \
		echo "tooling tests must not contain skip paths" >&2; \
		exit 1; \
	fi

unit-check: no-skips
	cd "$(REPO_ROOT)" && \
		FIR_TOOLING_TMPDIR="$(FIR_TOOLING_TMPDIR)" \
		node --test \
			tooling/worktree-temp-unit.test.mjs \
			tooling/wasm/function-index-unit.test.mjs \
			tooling/profile/node-profile-unit.test.mjs

binaryen-check:
	@for tool in wasm-as wasm-opt; do \
		path="$(FIR_BINARYEN_DIR)/$$tool"; \
		if ! test -x "$$path"; then \
			echo "missing pinned Binaryen tool: $$path" >&2; \
			echo "set FIR_BINARYEN_DIR to Emscripten 5.0.3's upstream/bin directory" >&2; \
			exit 1; \
		fi; \
		actual="$$($$path --version)"; \
		expected="$$tool $(BINARYEN_REVISION)"; \
		if test "$$actual" != "$$expected"; then \
			echo "Binaryen revision mismatch for $$tool" >&2; \
			echo "expected: $$expected" >&2; \
			echo "actual:   $$actual" >&2; \
			exit 1; \
		fi; \
	done

wasm-check: unit-check binaryen-check
	cd "$(REPO_ROOT)" && \
		FIR_BINARYEN_DIR="$(FIR_BINARYEN_DIR)" \
		FIR_TOOLING_TMPDIR="$(FIR_TOOLING_TMPDIR)" \
		node --test tooling/wasm/function-index.test.mjs

profile-check: unit-check binaryen-check
	cd "$(REPO_ROOT)" && \
		FIR_BINARYEN_DIR="$(FIR_BINARYEN_DIR)" \
		FIR_TOOLING_TMPDIR="$(FIR_TOOLING_TMPDIR)" \
		node --test tooling/profile/node-profile.test.mjs

array-probe-check: binaryen-check
	cd "$(ARRAY_PROBE_DIR)" && \
		LAKE_CACHE_DIR="$(FIR_LAKE_CACHE_DIR)" \
		LAKE_ARTIFACT_CACHE=true \
		LAKE_RESTORE_ARTIFACTS=true \
		lake build FirArrayProbe && \
		LAKE_CACHE_DIR="$(FIR_LAKE_CACHE_DIR)" \
		LAKE_ARTIFACT_CACHE=true \
		LAKE_RESTORE_ARTIFACTS=true \
		lake env lean Emit.lean && \
		node check.mjs _build/array-probe.raw.wasm && \
		FIR_BINARYEN_DIR="$(FIR_BINARYEN_DIR)" \
		FIR_TOOLING_TMPDIR="$(FIR_TOOLING_TMPDIR)" \
		node build.mjs && \
		node check.mjs _build/package/array-probe.wasm && \
		node ../wasm/function-index.mjs verify \
			--wasm _build/package/array-probe.wasm \
			--sidecar _build/package/array-probe.wasm.functions.json

check: wasm-check profile-check array-probe-check
