#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
first="$(mktemp -d)"
second="$(mktemp -d)"
trap 'rm -rf "$first" "$second"' EXIT

cd "$here"
lake build
lake -d .. build FirTalos.Differential
lake -d ../../.. build Fir.Wasm.Emit.SourceExamples
lake -d ../../.. env lean FirWasmSourceExample.lean
test -s _build/source-uint64.wasm
test -s _build/source-uint64.wasm.json
test -s _build/source-uint64.wasm.lcnf
cp _build/source-uint64.wasm _build/source-uint64-first.wasm
cp _build/source-uint64.wasm.json _build/source-uint64-first.wasm.json
cp _build/source-uint64.wasm.lcnf _build/source-uint64-first.wasm.lcnf
lake -d ../../.. env lean FirWasmSourceExample.lean
cmp _build/source-uint64-first.wasm _build/source-uint64.wasm
cmp _build/source-uint64-first.wasm.json _build/source-uint64.wasm.json
cmp _build/source-uint64-first.wasm.lcnf _build/source-uint64.wasm.lcnf
node --input-type=module -e '
  import fs from "node:fs";
  const path = process.argv[1];
  const bytes = fs.readFileSync(path);
  const manifest = JSON.parse(fs.readFileSync(path + ".json", "utf8"));
  if (!WebAssembly.validate(bytes)) process.exit(1);
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const result = instance.exports[manifest.entry]();
  if (BigInt.asUintN(64, result) !== 0xffffffffffffffffn) process.exit(1);
' _build/source-uint64.wasm
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
