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
for source in source-uint64 source-usize-id; do
  test -s "_build/$source.wasm"
  test -s "_build/$source.wasm.json"
  test -s "_build/$source.wasm.lcnf"
  cp "_build/$source.wasm" "_build/$source-first.wasm"
  cp "_build/$source.wasm.json" "_build/$source-first.wasm.json"
  cp "_build/$source.wasm.lcnf" "_build/$source-first.wasm.lcnf"
done
lake -d ../../.. env lean FirWasmSourceExample.lean
for source in source-uint64 source-usize-id; do
  cmp "_build/$source-first.wasm" "_build/$source.wasm"
  cmp "_build/$source-first.wasm.json" "_build/$source.wasm.json"
  cmp "_build/$source-first.wasm.lcnf" "_build/$source.wasm.lcnf"
done
node --input-type=module -e '
  import fs from "node:fs";
  const cases = [
    [process.argv[1], 0xffffffffffffffffn],
    [process.argv[2], 42n],
  ];
  function physicalArgument(kind, argument) {
    if (kind === "usize" && argument.kind === "usize") {
      return BigInt(argument.value);
    }
    throw new Error(`unsupported source argument ${kind}/${argument.kind}`);
  }
  for (const [path, expected] of cases) {
    const bytes = fs.readFileSync(path);
    const manifest = JSON.parse(fs.readFileSync(path + ".json", "utf8"));
    if (!WebAssembly.validate(bytes)) process.exit(1);
    if (manifest.params.length !== manifest.arguments.length) process.exit(1);
    const args = manifest.params.map((kind, index) =>
      physicalArgument(kind, manifest.arguments[index]));
    const { instance } = await WebAssembly.instantiate(bytes, {});
    const result = instance.exports[manifest.entry](...args);
    if (BigInt.asUintN(64, result) !== expected) process.exit(1);
  }
' _build/source-uint64.wasm _build/source-usize-id.wasm
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
