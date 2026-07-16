.PHONY: build examples inspect bug-cards no-placeholders check beam talos-setup talos-check clean

build:
	lake build

examples:
	lake env lean Fir/LeanIR/LegacyExamples.lean
	lake env lean Fir/LeanIR/InterpreterExamples.lean
	lake env lean Fir/Wasm/Examples.lean

inspect:
	lake lean Inspect

no-placeholders:
	@if rg -n "sorry|admit" Fir docs Inspect; then \
		echo "Found proof placeholders"; \
		exit 1; \
	fi

bug-cards:
	python3 scripts/validate_bug_cards.py

check: build examples inspect bug-cards no-placeholders

beam:
	lean-beam sync Fir/LeanIR.lean
	lean-beam sync Fir/Wasm.lean
	lean-beam sync Fir.lean
	lean-beam sync Fir/LeanIR/LegacyExamples.lean
	lean-beam sync Fir/LeanIR/InterpreterExamples.lean
	lean-beam sync Fir/Wasm/Examples.lean
	lean-beam sync Inspect

talos-setup:
	bash scripts/setup-talos.sh
	lake -d integration/talos update

talos-check:
	lake -d integration/talos build

clean:
	lake clean
