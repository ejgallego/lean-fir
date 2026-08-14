TOOLING_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(TOOLING_DIR)/..)
FIR_BINARYEN_DIR ?= $(REPO_ROOT)/.deps/lcnf-c-wasm/emsdk/upstream/bin
BINARYEN_REVISION := version 128 (version_127-18-g2eb472cd6)

.PHONY: no-skips unit-check binaryen-check wasm-check check

no-skips:
	@if rg -n 'test[.]skip|skip[[:space:]]*:' "$(TOOLING_DIR)" \
		--glob '*.test.mjs'; then \
		echo "tooling tests must not contain skip paths" >&2; \
		exit 1; \
	fi

unit-check: no-skips
	cd "$(REPO_ROOT)" && \
		node --test tooling/wasm/function-index-unit.test.mjs

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
		node --test tooling/wasm/function-index.test.mjs

check: wasm-check
