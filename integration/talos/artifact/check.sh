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
  source-string-input
  source-nat-list-case
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
  import assert from "node:assert/strict";
  import fs from "node:fs";
  import { SemanticHost, manifestValue } from "./run-artifacts.mjs";
  const cases = [
    [process.argv[1], "uint64", [], 0xffffffffffffffffn],
    [process.argv[2], "usize", ["usize"], 42n],
    [process.argv[3], "uint8", ["uint8"], 0xffn],
    [process.argv[4], "uint16", ["uint16"], 0xffffn],
    [process.argv[5], "uint32", ["uint32"], 0xffffffffn],
    [process.argv[6], "uint64", ["uint64"], 0xffffffffffffffffn],
    [process.argv[7], "uint64", ["object"], 0xffffffffffffffffn, "hello α_world_β"],
    [process.argv[8], "uint64", ["tobject"], 1n, undefined,
      [0n, 18446744073709551616n, 42n]],
  ];
  function decodeNat(host, value) {
    if (value.kind === "tagged") return value.payload;
    assert.equal(value.kind, "heap");
    const object = host.liveCell(value.location).object;
    assert.equal(object.kind, "natural");
    return object.value;
  }
  function decodeNatList(host, value) {
    const result = [];
    while (value.kind !== "tagged" || value.payload !== 0n) {
      assert.equal(value.kind, "heap");
      const object = host.liveCell(value.location).object;
      assert.equal(object.kind, "ctor");
      assert.equal(object.tag, 1n);
      assert.equal(object.objectFields.length, 2);
      result.push(decodeNat(host, object.objectFields[0]));
      value = object.objectFields[1];
    }
    return result;
  }
  for (const [path, kind, params, expected, initialString, initialNatList] of cases) {
    const bytes = fs.readFileSync(path);
    const manifest = JSON.parse(fs.readFileSync(path + ".json", "utf8"));
    assert.ok(WebAssembly.validate(bytes), `${path} failed WebAssembly validation`);
    assert.equal(manifest.result, kind);
    assert.deepStrictEqual(manifest.params, params);
    assert.equal(manifest.arguments.length, params.length);
    const host = new SemanticHost(manifest.initialRuntime);
    if (initialString !== undefined) {
      const argument = manifestValue(manifest.arguments[0]);
      assert.equal(argument.kind, "heap");
      assert.deepStrictEqual(host.liveCell(argument.location).object,
        { kind: "string", value: initialString });
    }
    if (initialNatList !== undefined) {
      assert.deepStrictEqual(
        decodeNatList(host, manifestValue(manifest.arguments[0])), initialNatList);
    }
    const args = manifest.params.map((kind, index) =>
      host.encode(kind, manifestValue(manifest.arguments[index])));
    const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
    const result = instance.exports[manifest.entry](...args);
    const decoded = host.decode(manifest.result, result);
    assert.equal(decoded.value, expected);
    console.log(`PASS source ${manifest.entry}`);
  }
' \
  _build/source-uint64.wasm \
  _build/source-usize-id.wasm \
  _build/source-uint8-id.wasm \
  _build/source-uint16-id.wasm \
  _build/source-uint32-id.wasm \
  _build/source-uint64-id.wasm \
  _build/source-string-input.wasm \
  _build/source-nat-list-case.wasm
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
