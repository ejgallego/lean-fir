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
source_artifacts=(
  source-uint64
  source-usize-id
  source-uint8-id
  source-uint16-id
  source-uint32-id
  source-uint64-id
)
for source in "${source_artifacts[@]}"; do
  test -s "_build/$source.wasm"
  test -s "_build/$source.wasm.json"
  test -s "_build/$source.wasm.lcnf"
  cp "_build/$source.wasm" "_build/$source-first.wasm"
  cp "_build/$source.wasm.json" "_build/$source-first.wasm.json"
  cp "_build/$source.wasm.lcnf" "_build/$source-first.wasm.lcnf"
done
lake -d ../../.. env lean FirWasmSourceExample.lean
for source in "${source_artifacts[@]}"; do
  cmp "_build/$source-first.wasm" "_build/$source.wasm"
  cmp "_build/$source-first.wasm.json" "_build/$source.wasm.json"
  cmp "_build/$source-first.wasm.lcnf" "_build/$source.wasm.lcnf"
done
node --input-type=module -e '
  import fs from "node:fs";
  const cases = [
    [process.argv[1], "uint64", 64, 0, 0xffffffffffffffffn],
    [process.argv[2], "usize", 64, 1, 42n],
    [process.argv[3], "uint8", 8, 1, 0xffn],
    [process.argv[4], "uint16", 16, 1, 0xffffn],
    [process.argv[5], "uint32", 32, 1, 0xffffffffn],
    [process.argv[6], "uint64", 64, 1, 0xffffffffffffffffn],
  ];
  function physicalArgument(kind, argument) {
    if (kind === "usize" && argument.kind === "usize") {
      return BigInt(argument.value);
    }
    if (["uint8", "uint16", "uint32", "uint64"].includes(kind) &&
        argument.kind === "scalar" && argument.scalarKind === kind) {
      const value = BigInt(argument.value);
      return kind === "uint64" ? value : Number(value);
    }
    throw new Error(`unsupported source argument ${kind}/${argument.kind}`);
  }
  for (const [path, kind, width, arity, expected] of cases) {
    const bytes = fs.readFileSync(path);
    const manifest = JSON.parse(fs.readFileSync(path + ".json", "utf8"));
    if (!WebAssembly.validate(bytes)) process.exit(1);
    if (manifest.result !== kind || manifest.params.length !== arity ||
        manifest.arguments.length !== arity ||
        (arity === 1 && manifest.params[0] !== kind)) process.exit(1);
    const args = manifest.params.map((kind, index) =>
      physicalArgument(kind, manifest.arguments[index]));
    const { instance } = await WebAssembly.instantiate(bytes, {});
    const result = instance.exports[manifest.entry](...args);
    const unsigned = BigInt.asUintN(width,
      typeof result === "bigint" ? result : BigInt(result));
    if (unsigned !== expected) process.exit(1);
    console.log(`PASS source ${manifest.entry}`);
  }
' \
  _build/source-uint64.wasm \
  _build/source-usize-id.wasm \
  _build/source-uint8-id.wasm \
  _build/source-uint16-id.wasm \
  _build/source-uint32-id.wasm \
  _build/source-uint64-id.wasm
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
