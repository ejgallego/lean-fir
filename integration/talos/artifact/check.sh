#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
first="$(mktemp -d)"
second="$(mktemp -d)"
trap 'rm -rf "$first" "$second"' EXIT

cd "$here"
lake build
lake -d .. build FirTalos.Differential
lake -d ../../.. build Fir.Wasm.Emit.SourceExamples Fir.Wasm.Emit.Command
lake -d ../../.. env lean FirWasmSourceExample.lean
source_artifacts=(
  source-uint64
  source-nat
  source-usize-id
  source-usize-id-module
  source-uint8-id
  source-uint16-id
  source-uint32-id
  source-uint64-id
  source-string-input
  source-nat-list-case
  source-pretty-format
  source-pretty-format-coverage
  source-pretty-format-module
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
cmp _build/source-usize-id-module.wasm _build/source-usize-id.wasm
cmp _build/source-usize-id-module.wasm.lcnf _build/source-usize-id.wasm.lcnf
cmp _build/source-pretty-format-module.wasm _build/source-pretty-format.wasm
cmp _build/source-pretty-format-module.wasm.lcnf _build/source-pretty-format.wasm.lcnf
node --input-type=module -e '
  import assert from "node:assert/strict";
  import fs from "node:fs";
  import { SemanticHost, manifestValue } from "../../../scripts/wasm_semantic_host.mjs";
  import { formatExternalRegistry } from "../../../scripts/wasm_format_externals.mjs";
  const cases = [
    [process.argv[1], "uint64", [], 0xffffffffffffffffn],
    [process.argv[2], "tobject", [], 42n],
    [process.argv[3], "usize", ["usize"], 42n],
    [process.argv[4], "uint8", ["uint8"], 0xffn],
    [process.argv[5], "uint16", ["uint16"], 0xffffn],
    [process.argv[6], "uint32", ["uint32"], 0xffffffffn],
    [process.argv[7], "uint64", ["uint64"], 0xffffffffffffffffn],
    [process.argv[8], "uint64", ["object"], 0xffffffffffffffffn, "hello α_world_β"],
    [process.argv[9], "uint64", ["tobject"], 1n, undefined,
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
    const actual = decoded.kind === "tagged" ? decoded.payload : decoded.value;
    assert.equal(actual, expected);
    console.log(`PASS source ${manifest.entry}`);
  }
  const formatCases = [
    [process.argv[10], "hello\n  world"],
    [process.argv[11], "α β\n. γ\n  δ\n  ε"],
  ];
  for (const [path, expected] of formatCases) {
    const bytes = fs.readFileSync(path);
    const manifest = JSON.parse(fs.readFileSync(path + ".json", "utf8"));
    assert.ok(WebAssembly.validate(bytes), `${path} failed WebAssembly validation`);
    assert.equal(manifest.result, "object");
    assert.deepStrictEqual(manifest.params, ["tobject", "tobject", "tobject", "tobject"]);
    const host = new SemanticHost(manifest.initialRuntime, formatExternalRegistry);
    const args = manifest.params.map((kind, index) =>
      host.encode(kind, manifestValue(manifest.arguments[index])));
    const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
    const result = host.decode(manifest.result, instance.exports[manifest.entry](...args));
    assert.equal(result.kind, "heap");
    assert.deepStrictEqual(host.liveCell(result.location).object,
      { kind: "string", value: expected });
    assert.ok(!host.trace.some((event) => event.name === "panicCore" ||
      event.name === "instInhabitedOfMonad._redArg"));
    console.log(`PASS source ${manifest.entry}`);
  }
' \
  _build/source-uint64.wasm \
  _build/source-nat.wasm \
  _build/source-usize-id.wasm \
  _build/source-uint8-id.wasm \
  _build/source-uint16-id.wasm \
  _build/source-uint32-id.wasm \
  _build/source-uint64-id.wasm \
  _build/source-string-input.wasm \
  _build/source-nat-list-case.wasm \
  _build/source-pretty-format.wasm \
  _build/source-pretty-format-coverage.wasm
node call-pretty-format.mjs _build/source-pretty-format-module.wasm
node test-module-client.mjs \
  _build/source-usize-id-module.wasm \
  _build/source-usize-id.wasm
node test-module-fetch.mjs _build/source-usize-id-module.wasm
node test-semantic-host.mjs
if [[ -n "${FIR_BROWSER:-}" ]]; then
  make -C "$here/../../.." validate-v8
  ./browser-check.sh "$FIR_BROWSER"
  ./browser-validation-check.sh "$FIR_BROWSER"
fi
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
