.PHONY: build examples inspect no-placeholders check beam clean

build:
	lake build

examples:
	lake env lean Fir/LeanIR/Examples.lean

inspect:
	lake lean Inspect

no-placeholders:
	@if rg -n "sorry|admit" Fir docs Inspect; then \
		echo "Found proof placeholders"; \
		exit 1; \
	fi

check: build examples inspect no-placeholders

beam:
	lean-beam sync Fir/LeanIR/LCNFCore.lean
	lean-beam sync Fir/LeanIR/Examples.lean
	lean-beam sync Inspect

clean:
	lake clean
