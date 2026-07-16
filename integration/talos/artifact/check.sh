#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
first="$(mktemp -d)"
second="$(mktemp -d)"
trap 'rm -rf "$first" "$second"' EXIT

cd "$here"
lake build
lake -d .. build FirTalos.Differential
lake exe fir-wasm-artifact all "$first"
lake exe fir-wasm-artifact all "$second"
lake -d .. env lean --run ../FirWasmOracleMain.lean all "$first"
lake -d .. env lean --run ../FirWasmOracleMain.lean all "$second"

for manifest in "$first"/*.wasm.json; do
  name="$(basename "$manifest" .wasm.json)"
  cmp "$first/$name.wasm" "$second/$name.wasm"
  cmp "$first/$name.wasm.json" "$second/$name.wasm.json"
  cmp "$first/$name.expected.json" "$second/$name.expected.json"
done

node run-artifacts.mjs "$first"
