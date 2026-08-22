#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
mkdir -p "$here/_build/tmp"
export TMPDIR="$here/_build/tmp"
exhaustive_pretty="${FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS:-0}"
if [[ "$exhaustive_pretty" != 0 && "$exhaustive_pretty" != 1 ]]; then
  echo "FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS must be 0 or 1" >&2
  exit 1
fi
if [[ -n "${FIR_BROWSER:-}" && "$exhaustive_pretty" != 1 ]]; then
  echo "FIR_BROWSER requires FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1" >&2
  exit 1
fi
first="$(mktemp -d)"
second="$(mktemp -d)"
trap 'rm -rf "$first" "$second"' EXIT

cd "$here"
node --test "$root/integration/package-tools/immutable-package.test.mjs"
node --test "$root/integration/package-tools/verified-package.test.mjs"
node --test "$root/integration/package-tools/postponed-source-view.test.mjs"
node instruction-provenance-fixture/check.mjs \
  "$root/.deps/lcnf-c-wasm/emsdk/upstream/bin" \
  "$here/_build/instruction-provenance-fixture"
lake build
lake exe fir-wasm-artifact resident-global _build/resident-global.wasm
node run-resident-global.mjs _build/resident-global.wasm
lake exe fir-wasm-artifact resident-memory-surface \
  _build/resident-memory-surface.wasm
node run-resident-memory-surface.mjs _build/resident-memory-surface.wasm
lake exe fir-wasm-artifact resident-allocator _build/resident-allocator.wasm
node run-resident-allocator.mjs _build/resident-allocator.wasm
lake exe fir-wasm-artifact resident-arrays _build/resident-arrays.wasm
node run-resident-arrays.mjs _build/resident-arrays.wasm
lake exe fir-wasm-artifact resident-byte-arrays \
  _build/resident-byte-arrays.wasm
node run-resident-byte-array.mjs _build/resident-byte-arrays.wasm
lake exe fir-wasm-artifact resident-fixed-width \
  _build/resident-fixed-width.wasm
node run-resident-fixed-width.mjs _build/resident-fixed-width.wasm
lake exe fir-wasm-artifact resident-float _build/resident-float.wasm
node run-resident-float.mjs _build/resident-float.wasm
lake exe fir-wasm-artifact resident-libm-frontier \
  _build/resident-libm-frontier.wasm
emcc="$root/.deps/lcnf-c-wasm/emsdk/upstream/emscripten/emcc"
libm_linker="$root/integration/wasm-runtime/link-runtime.mjs"
libm_source="$root/integration/wasm-runtime/libm-runtime.c"
"$emcc" "$libm_source" -O3 -flto --no-entry -sSTANDALONE_WASM=1 \
  -sIMPORTED_MEMORY=1 -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=65536 \
  -sSTACK_SIZE=16384 -Wl,--gc-sections -Wl,--strip-all \
  -o _build/resident-libm-runtime.wasm
node "$libm_linker" _build/resident-libm-frontier.wasm \
  _build/resident-libm-runtime.wasm _build/resident-libm-complete.wasm
"$emcc" "$libm_source" -O3 -flto --no-entry -sSTANDALONE_WASM=1 \
  -sIMPORTED_MEMORY=1 -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=65536 \
  -sSTACK_SIZE=16384 -Wl,--gc-sections -Wl,--strip-all \
  -o _build/resident-libm-runtime-repeat.wasm
node "$libm_linker" _build/resident-libm-frontier.wasm \
  _build/resident-libm-runtime-repeat.wasm \
  _build/resident-libm-complete-repeat.wasm
cmp _build/resident-libm-runtime.wasm \
  _build/resident-libm-runtime-repeat.wasm
cmp _build/resident-libm-complete.wasm \
  _build/resident-libm-complete-repeat.wasm
node run-resident-libm.mjs _build/resident-libm-frontier.wasm \
  _build/resident-libm-complete.wasm
lake exe fir-wasm-float-source _build/source-float-conversions.wasm
node run-source-float.mjs _build/source-float-conversions.wasm
for suffix in wasm wasm.json wasm.lcnf wasm.inventory.json wasm.oracle.json; do
  cp "_build/source-float-conversions.$suffix" \
    "_build/source-float-conversions-first.$suffix"
done
lake exe fir-wasm-float-source _build/source-float-conversions.wasm
node run-source-float.mjs _build/source-float-conversions.wasm
for suffix in wasm wasm.json wasm.lcnf wasm.inventory.json wasm.oracle.json; do
  cmp "_build/source-float-conversions-first.$suffix" \
    "_build/source-float-conversions.$suffix"
done
lake exe fir-wasm-artifact resident-constructors \
  _build/resident-constructors.wasm
node run-resident-constructors.mjs _build/resident-constructors.wasm
lake exe fir-wasm-artifact resident-closure-allocation \
  _build/resident-closure-allocation.wasm
node run-resident-closure-allocation.mjs \
  _build/resident-closure-allocation.wasm
lake exe fir-wasm-artifact resident-scalar-box \
  _build/resident-scalar-box.wasm
node run-resident-scalar-box.mjs _build/resident-scalar-box.wasm
lake exe fir-wasm-artifact resident-literals \
  _build/resident-literals.wasm
node run-resident-literals.mjs _build/resident-literals.wasm
lake exe fir-wasm-artifact resident-setters \
  _build/resident-setters.wasm
node run-resident-setters.mjs _build/resident-setters.wasm
lake exe fir-wasm-artifact resident-tag-setter \
  _build/resident-tag-setter.wasm
node run-resident-tag-setter.mjs _build/resident-tag-setter.wasm
lake exe fir-wasm-artifact resident-increments \
  _build/resident-increments.wasm
node run-resident-increments.mjs _build/resident-increments.wasm
lake exe fir-wasm-artifact resident-releases \
  _build/resident-releases.wasm
node run-resident-releases.mjs _build/resident-releases.wasm
lake exe fir-wasm-artifact resident-cache \
  _build/resident-cache.wasm
node run-resident-cache.mjs _build/resident-cache.wasm
lake exe fir-wasm-artifact resident-numeric \
  _build/resident-numeric.wasm
node run-resident-numeric.mjs _build/resident-numeric.wasm
lake exe fir-wasm-artifact resident-big-numeric \
  _build/resident-big-numeric.wasm
node run-resident-big-numeric.mjs _build/resident-big-numeric.wasm
lake exe fir-wasm-artifact resident-nat-arithmetic \
  _build/resident-nat-arithmetic.wasm
node run-resident-nat-arithmetic.mjs _build/resident-nat-arithmetic.wasm
lake exe fir-wasm-artifact resident-platform \
  _build/resident-platform.wasm
node run-resident-platform.mjs _build/resident-platform.wasm
lake exe fir-wasm-artifact resident-string \
  _build/resident-string.wasm
node run-resident-string.mjs _build/resident-string.wasm \
  --require-usize-repr --require-of-list
lake exe fir-wasm-artifact resident-fallbacks \
  _build/resident-fallbacks.wasm
node run-resident-fallbacks.mjs _build/resident-fallbacks.wasm
lake exe fir-wasm-artifact resident-get-tag _build/resident-get-tag.wasm
node run-resident-get-tag.mjs _build/resident-get-tag.wasm
lake exe fir-wasm-artifact resident-is-shared _build/resident-is-shared.wasm
node run-resident-is-shared.mjs _build/resident-is-shared.wasm
lake exe fir-wasm-artifact resident-read-projections \
  _build/resident-read-projections.wasm
node run-resident-read-projections.mjs \
  _build/resident-read-projections.wasm
lake exe fir-wasm-artifact resident-closure-projections \
  _build/resident-closure-projections.wasm
node run-resident-closure-projections.mjs \
  _build/resident-closure-projections.wasm
lake exe fir-wasm-artifact resident-closure-matches \
  _build/resident-closure-matches.wasm
node run-resident-closure-matches.mjs \
  _build/resident-closure-matches.wasm
lake -d .. build FirTalos.Differential
lake -d ../../.. build Fir.Wasm.Emit.SourceExamples Fir.Wasm.Emit.Command \
  Fir.Wasm.Emit.ResidentPrettyFormat fir-prettyM-artifact
pretty_generator="$root/.lake/build/bin/fir-prettyM-artifact"
generate_source_artifacts() {
  if [[ "$exhaustive_pretty" == 1 ]]; then
    FIR_PRETTYM_CHECKPOINTS=1 lake -d "$root" env lean \
      "$here/FirWasmSourceExample.lean"
    FIR_PRETTYM_CHECKPOINTS=1 lake -d "$root" env lean \
      "$here/FirWasmPrettyTraceExample.lean"
    env -u FIR_PRETTYM_CHECKPOINTS lake -d "$root" env "$pretty_generator" \
      --instruction-origins \
      "$here/_build/source-pretty-format-trace-resident-closed.origins.json" \
      --function-inventory \
      "$here/_build/source-pretty-format-trace-resident-closed.wasm.inventory.json" \
      "$here/FirWasmPrettyTraceExample.lean" \
      "$here/_build/source-pretty-format-trace-resident-closed.wasm"
  else
    env -u FIR_PRETTYM_CHECKPOINTS lake -d "$root" env "$pretty_generator" \
      "$here/FirWasmSourceExample.lean" FirWasmSourceExample \
      Fir.Wasm.Emit.SourceFixture.prettyFormatRaw \
      "$here/_build/source-pretty-format-resident-closed.wasm"
    env -u FIR_PRETTYM_CHECKPOINTS lake -d "$root" env "$pretty_generator" \
      --instruction-origins \
      "$here/_build/source-pretty-format-trace-resident-closed.origins.json" \
      --function-inventory \
      "$here/_build/source-pretty-format-trace-resident-closed.wasm.inventory.json" \
      "$here/FirWasmPrettyTraceExample.lean" \
      "$here/_build/source-pretty-format-trace-resident-closed.wasm"
  fi
  node "$root/tooling/wasm/function-index.mjs" direct \
    --binaryen-dir "$root/.deps/lcnf-c-wasm/emsdk/upstream/bin" \
    --wasm "$here/_build/source-pretty-format-trace-resident-closed.wasm" \
    --inventory \
      "$here/_build/source-pretty-format-trace-resident-closed.wasm.inventory.json" \
    --output \
      "$here/_build/source-pretty-format-trace-resident-closed.wasm.functions.json"
}
generate_source_artifacts
test -s _build/source-pretty-format-trace-resident-closed.origins.json
test -s _build/source-pretty-format-trace-resident-closed.wasm.inventory.json
test -s _build/source-pretty-format-trace-resident-closed.wasm.functions.json
cp _build/source-pretty-format-trace-resident-closed.origins.json \
  _build/source-pretty-format-trace-resident-closed-first.origins.json
cp _build/source-pretty-format-trace-resident-closed.wasm.inventory.json \
  _build/source-pretty-format-trace-resident-closed-first.wasm.inventory.json
cp _build/source-pretty-format-trace-resident-closed.wasm.functions.json \
  _build/source-pretty-format-trace-resident-closed-first.wasm.functions.json
mapfile -t source_artifacts < <(
  node --input-type=module -e '
    import { CONCRETE_SOURCE_PROBES } from "./concrete-corpus.mjs";
    console.log(CONCRETE_SOURCE_PROBES.join("\n"));
  '
)
for source in "${source_artifacts[@]}"; do
  test -s "_build/$source.wasm"
  test -s "_build/$source.wasm.json"
  test -s "_build/$source.wasm.lcnf"
  cp "_build/$source.wasm" "_build/$source-first.wasm"
  cp "_build/$source.wasm.json" "_build/$source-first.wasm.json"
  cp "_build/$source.wasm.lcnf" "_build/$source-first.wasm.lcnf"
done
if [[ "$exhaustive_pretty" == 1 ]]; then
  resident_pretties=(
    "source-pretty-format-resident-get-tag"
    "source-pretty-format-resident-runtime"
    "source-pretty-format-resident-projections"
    "source-pretty-format-resident-closure-projections"
    "source-pretty-format-resident-closure-matches"
    "source-pretty-format-resident-allocator"
    "source-pretty-format-resident-constructors"
    "source-pretty-format-resident-naturals"
    "source-pretty-format-resident-partial-applications"
    "source-pretty-format-resident-setters"
    "source-pretty-format-resident-increments"
    "source-pretty-format-resident-releases"
    "source-pretty-format-resident-cache"
    "source-pretty-format-resident-numeric"
    "source-pretty-format-resident-big-numeric"
    "source-pretty-format-resident-string"
    "source-pretty-format-resident-closed"
    "source-pretty-format-trace-resident-constructors"
    "source-pretty-format-trace-resident-naturals"
    "source-pretty-format-trace-resident-partial-applications"
    "source-pretty-format-trace-resident-setters"
    "source-pretty-format-trace-resident-increments"
    "source-pretty-format-trace-resident-releases"
    "source-pretty-format-trace-resident-tag-setters"
    "source-pretty-format-trace-resident-cache"
    "source-pretty-format-trace-resident-numeric"
    "source-pretty-format-trace-resident-big-numeric"
    "source-pretty-format-trace-resident-string"
    "source-pretty-format-trace-resident-closed"
  )
else
  resident_pretties=(
    "source-pretty-format-resident-closed"
    "source-pretty-format-trace-resident-closed"
  )
fi
for resident_pretty in "${resident_pretties[@]}"; do
  for suffix in wasm wasm.json wasm.lcnf; do
    test -s "_build/$resident_pretty.$suffix"
    cp "_build/$resident_pretty.$suffix" "_build/$resident_pretty-first.$suffix"
  done
done
generate_source_artifacts
cmp _build/source-pretty-format-trace-resident-closed-first.origins.json \
  _build/source-pretty-format-trace-resident-closed.origins.json
cmp _build/source-pretty-format-trace-resident-closed-first.wasm.inventory.json \
  _build/source-pretty-format-trace-resident-closed.wasm.inventory.json
cmp _build/source-pretty-format-trace-resident-closed-first.wasm.functions.json \
  _build/source-pretty-format-trace-resident-closed.wasm.functions.json
node check-instruction-origins.mjs \
  _build/source-pretty-format-trace-resident-closed.wasm \
  _build/source-pretty-format-trace-resident-closed.origins.json
node "$root/tooling/wasm/function-index.mjs" verify \
  --wasm _build/source-pretty-format-trace-resident-closed.wasm \
  --sidecar _build/source-pretty-format-trace-resident-closed.wasm.functions.json
for source in "${source_artifacts[@]}"; do
  cmp "_build/$source-first.wasm" "_build/$source.wasm"
  cmp "_build/$source-first.wasm.json" "_build/$source.wasm.json"
  cmp "_build/$source-first.wasm.lcnf" "_build/$source.wasm.lcnf"
done
for resident_pretty in "${resident_pretties[@]}"; do
  for suffix in wasm wasm.json wasm.lcnf; do
    cmp "_build/$resident_pretty-first.$suffix" "_build/$resident_pretty.$suffix"
  done
done
cmp _build/source-usize-id-module.wasm _build/source-usize-id.wasm
cmp _build/source-usize-id-module.wasm.lcnf _build/source-usize-id.wasm.lcnf
cmp _build/source-float32-id-module.wasm _build/source-float32-id.wasm
cmp _build/source-float32-id-module.wasm.lcnf _build/source-float32-id.wasm.lcnf
cmp _build/source-float64-id-module.wasm _build/source-float64-id.wasm
cmp _build/source-float64-id-module.wasm.lcnf _build/source-float64-id.wasm.lcnf
cmp _build/source-pretty-format-module.wasm _build/source-pretty-format.wasm
cmp _build/source-pretty-format-module.wasm.lcnf _build/source-pretty-format.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-closed.wasm.lcnf
if [[ "$exhaustive_pretty" == 1 ]]; then
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-get-tag.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-runtime.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-projections.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-closure-projections.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-closure-matches.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-allocator.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-constructors.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-naturals.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-partial-applications.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-setters.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-increments.wasm.lcnf
cmp _build/source-pretty-format-module.wasm.lcnf \
  _build/source-pretty-format-resident-releases.wasm.lcnf
cmp _build/source-pretty-format-resident-releases.wasm.lcnf \
  _build/source-pretty-format-resident-cache.wasm.lcnf
cmp _build/source-pretty-format-resident-cache.wasm.lcnf \
  _build/source-pretty-format-resident-numeric.wasm.lcnf
cmp _build/source-pretty-format-resident-numeric.wasm.lcnf \
  _build/source-pretty-format-resident-big-numeric.wasm.lcnf
cmp _build/source-pretty-format-resident-big-numeric.wasm.lcnf \
  _build/source-pretty-format-resident-string.wasm.lcnf
cmp _build/source-pretty-format-resident-string.wasm.lcnf \
  _build/source-pretty-format-resident-closed.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-naturals.wasm.lcnf \
  _build/source-pretty-format-trace-resident-partial-applications.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-partial-applications.wasm.lcnf \
  _build/source-pretty-format-trace-resident-setters.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-setters.wasm.lcnf \
  _build/source-pretty-format-trace-resident-increments.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-increments.wasm.lcnf \
  _build/source-pretty-format-trace-resident-releases.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-releases.wasm.lcnf \
  _build/source-pretty-format-trace-resident-tag-setters.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-tag-setters.wasm.lcnf \
  _build/source-pretty-format-trace-resident-cache.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-cache.wasm.lcnf \
  _build/source-pretty-format-trace-resident-numeric.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-numeric.wasm.lcnf \
  _build/source-pretty-format-trace-resident-big-numeric.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-big-numeric.wasm.lcnf \
  _build/source-pretty-format-trace-resident-string.wasm.lcnf
cmp _build/source-pretty-format-trace-resident-string.wasm.lcnf \
  _build/source-pretty-format-trace-resident-closed.wasm.lcnf
node check-resident-pretty-format.mjs \
  _build/source-pretty-format-module.wasm \
  _build/source-pretty-format-resident-get-tag.wasm \
  _build/source-pretty-format-resident-runtime.wasm \
  _build/source-pretty-format-resident-projections.wasm \
  _build/source-pretty-format-resident-closure-projections.wasm \
  _build/source-pretty-format-resident-closure-matches.wasm \
  _build/source-pretty-format-resident-allocator.wasm \
  _build/source-pretty-format-resident-constructors.wasm \
  _build/source-pretty-format-resident-naturals.wasm \
  _build/source-pretty-format-resident-partial-applications.wasm \
  _build/source-pretty-format-resident-setters.wasm \
  _build/source-pretty-format-resident-increments.wasm \
  _build/source-pretty-format-resident-releases.wasm \
  _build/source-pretty-format-trace-resident-releases.wasm \
  _build/source-pretty-format-trace-resident-tag-setters.wasm \
  _build/source-pretty-format-resident-cache.wasm \
  _build/source-pretty-format-trace-resident-cache.wasm \
  _build/source-pretty-format-resident-numeric.wasm \
  _build/source-pretty-format-trace-resident-numeric.wasm \
  _build/source-pretty-format-resident-big-numeric.wasm \
  _build/source-pretty-format-trace-resident-big-numeric.wasm \
  _build/source-pretty-format-resident-string.wasm \
  _build/source-pretty-format-trace-resident-string.wasm \
  _build/source-pretty-format-resident-closed.wasm \
  _build/source-pretty-format-trace-resident-closed.wasm
node run-resident-numeric.mjs \
  _build/source-pretty-format-resident-numeric.wasm
node run-resident-numeric.mjs \
  _build/source-pretty-format-trace-resident-numeric.wasm
node run-resident-big-numeric.mjs \
  _build/source-pretty-format-resident-big-numeric.wasm
node run-resident-big-numeric.mjs \
  _build/source-pretty-format-trace-resident-big-numeric.wasm
node run-resident-big-numeric.mjs \
  _build/source-pretty-format-resident-string.wasm
node run-resident-big-numeric.mjs \
  _build/source-pretty-format-trace-resident-string.wasm
node run-resident-string.mjs \
  _build/source-pretty-format-resident-string.wasm
node run-resident-string.mjs \
  _build/source-pretty-format-trace-resident-string.wasm
fi
node run-resident-string.mjs \
  _build/source-pretty-format-resident-closed.wasm
node run-resident-string.mjs \
  _build/source-pretty-format-trace-resident-closed.wasm
node run-resident-big-numeric.mjs \
  _build/source-pretty-format-resident-closed.wasm
node run-resident-big-numeric.mjs \
  _build/source-pretty-format-trace-resident-closed.wasm
node run-resident-fallbacks.mjs \
  _build/source-pretty-format-resident-closed.wasm
node run-resident-fallbacks.mjs \
  _build/source-pretty-format-trace-resident-closed.wasm
node --input-type=module -e '
  import assert from "node:assert/strict";
  import fs from "node:fs";
  import { SemanticHost, manifestValue } from "../../../scripts/wasm_semantic_host.mjs";
  import { formatExternalRegistry } from "../../../scripts/wasm_format_externals.mjs";
  const cases = [
    [process.argv[1], "uint64", [], 0xffffffffffffffffn],
    [process.argv[2], "tagged", [], 42n],
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
node call-concrete-pretty-format.mjs _build/source-pretty-format-module.wasm
if [[ "$exhaustive_pretty" == 1 ]]; then
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-get-tag.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-runtime.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-projections.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-closure-projections.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-closure-matches.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-allocator.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-constructors.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-naturals.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-partial-applications.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-setters.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-increments.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-releases.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-cache.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-numeric.wasm
fi
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-closed.wasm
./package-pretty-format.sh --no-build
node test-module-client.mjs \
  _build/source-usize-id-module.wasm \
  _build/source-usize-id.wasm \
  _build/source-float32-id-module.wasm \
  _build/source-float64-id-module.wasm
node test-module-fetch.mjs _build/source-usize-id-module.wasm
node test-semantic-host.mjs
node test-concrete-closure-dispatch.mjs
node test-concrete-floats.mjs
node test-concrete-format-externals.mjs
node test-concrete-initial-runtime.mjs
node run-concrete-source-artifacts.mjs _build
node call-concrete-pretty-format-invocation.mjs \
  _build/source-pretty-format-coverage.wasm
make -C "$here/../../.." validate-v8
node check-concrete-validation-products.mjs \
  "$here/../../../_build/validation-v8"
if [[ -n "${FIR_BROWSER:-}" ]]; then
  ./browser-check.sh "$FIR_BROWSER"
  ./browser-validation-check.sh "$FIR_BROWSER"
fi
lake exe fir-wasm-artifact all "$first"
lake exe fir-wasm-artifact all "$second"
lake exe fir-wasm-artifact resident-get-tag "$first/resident/get-tag.wasm"
lake exe fir-wasm-artifact resident-get-tag "$second/resident/get-tag.wasm"
cmp "$first/resident/get-tag.wasm" "$second/resident/get-tag.wasm"
cmp "$first/resident/get-tag.wasm.json" "$second/resident/get-tag.wasm.json"
lake exe fir-wasm-artifact resident-is-shared "$first/resident/is-shared.wasm"
lake exe fir-wasm-artifact resident-is-shared "$second/resident/is-shared.wasm"
cmp "$first/resident/is-shared.wasm" "$second/resident/is-shared.wasm"
cmp "$first/resident/is-shared.wasm.json" "$second/resident/is-shared.wasm.json"
lake exe fir-wasm-artifact resident-read-projections \
  "$first/resident/read-projections.wasm"
lake exe fir-wasm-artifact resident-read-projections \
  "$second/resident/read-projections.wasm"
cmp "$first/resident/read-projections.wasm" \
  "$second/resident/read-projections.wasm"
cmp "$first/resident/read-projections.wasm.json" \
  "$second/resident/read-projections.wasm.json"
lake exe fir-wasm-artifact resident-closure-projections \
  "$first/resident/closure-projections.wasm"
lake exe fir-wasm-artifact resident-closure-projections \
  "$second/resident/closure-projections.wasm"
cmp "$first/resident/closure-projections.wasm" \
  "$second/resident/closure-projections.wasm"
cmp "$first/resident/closure-projections.wasm.json" \
  "$second/resident/closure-projections.wasm.json"
lake exe fir-wasm-artifact resident-closure-matches \
  "$first/resident/closure-matches.wasm"
lake exe fir-wasm-artifact resident-closure-matches \
  "$second/resident/closure-matches.wasm"
cmp "$first/resident/closure-matches.wasm" \
  "$second/resident/closure-matches.wasm"
cmp "$first/resident/closure-matches.wasm.json" \
  "$second/resident/closure-matches.wasm.json"
lake exe fir-wasm-artifact resident-allocator \
  "$first/resident/allocator.wasm"
lake exe fir-wasm-artifact resident-allocator \
  "$second/resident/allocator.wasm"
cmp "$first/resident/allocator.wasm" "$second/resident/allocator.wasm"
cmp "$first/resident/allocator.wasm.json" \
  "$second/resident/allocator.wasm.json"
lake exe fir-wasm-artifact resident-closure-allocation \
  "$first/resident/closure-allocation.wasm"
lake exe fir-wasm-artifact resident-closure-allocation \
  "$second/resident/closure-allocation.wasm"
cmp "$first/resident/closure-allocation.wasm" \
  "$second/resident/closure-allocation.wasm"
cmp "$first/resident/closure-allocation.wasm.json" \
  "$second/resident/closure-allocation.wasm.json"
lake exe fir-wasm-artifact resident-literals \
  "$first/resident/literals.wasm"
lake exe fir-wasm-artifact resident-literals \
  "$second/resident/literals.wasm"
cmp "$first/resident/literals.wasm" "$second/resident/literals.wasm"
cmp "$first/resident/literals.wasm.json" \
  "$second/resident/literals.wasm.json"
lake exe fir-wasm-artifact resident-setters \
  "$first/resident/setters.wasm"
lake exe fir-wasm-artifact resident-setters \
  "$second/resident/setters.wasm"
cmp "$first/resident/setters.wasm" "$second/resident/setters.wasm"
cmp "$first/resident/setters.wasm.json" \
  "$second/resident/setters.wasm.json"
lake exe fir-wasm-artifact resident-tag-setter \
  "$first/resident/tag-setter.wasm"
lake exe fir-wasm-artifact resident-tag-setter \
  "$second/resident/tag-setter.wasm"
cmp "$first/resident/tag-setter.wasm" "$second/resident/tag-setter.wasm"
cmp "$first/resident/tag-setter.wasm.json" \
  "$second/resident/tag-setter.wasm.json"
lake exe fir-wasm-artifact resident-increments \
  "$first/resident/increments.wasm"
lake exe fir-wasm-artifact resident-increments \
  "$second/resident/increments.wasm"
cmp "$first/resident/increments.wasm" "$second/resident/increments.wasm"
cmp "$first/resident/increments.wasm.json" \
  "$second/resident/increments.wasm.json"
lake exe fir-wasm-artifact resident-releases \
  "$first/resident/releases.wasm"
lake exe fir-wasm-artifact resident-releases \
  "$second/resident/releases.wasm"
cmp "$first/resident/releases.wasm" "$second/resident/releases.wasm"
cmp "$first/resident/releases.wasm.json" \
  "$second/resident/releases.wasm.json"
lake exe fir-wasm-artifact resident-cache \
  "$first/resident/cache.wasm"
lake exe fir-wasm-artifact resident-cache \
  "$second/resident/cache.wasm"
cmp "$first/resident/cache.wasm" "$second/resident/cache.wasm"
cmp "$first/resident/cache.wasm.json" \
  "$second/resident/cache.wasm.json"
lake exe fir-wasm-artifact resident-numeric \
  "$first/resident/numeric.wasm"
lake exe fir-wasm-artifact resident-numeric \
  "$second/resident/numeric.wasm"
cmp "$first/resident/numeric.wasm" "$second/resident/numeric.wasm"
cmp "$first/resident/numeric.wasm.json" \
  "$second/resident/numeric.wasm.json"
lake exe fir-wasm-artifact resident-big-numeric \
  "$first/resident/big-numeric.wasm"
lake exe fir-wasm-artifact resident-big-numeric \
  "$second/resident/big-numeric.wasm"
cmp "$first/resident/big-numeric.wasm" "$second/resident/big-numeric.wasm"
cmp "$first/resident/big-numeric.wasm.json" \
  "$second/resident/big-numeric.wasm.json"
lake exe fir-wasm-artifact resident-nat-arithmetic \
  "$first/resident/nat-arithmetic.wasm"
lake exe fir-wasm-artifact resident-nat-arithmetic \
  "$second/resident/nat-arithmetic.wasm"
cmp "$first/resident/nat-arithmetic.wasm" \
  "$second/resident/nat-arithmetic.wasm"
cmp "$first/resident/nat-arithmetic.wasm.json" \
  "$second/resident/nat-arithmetic.wasm.json"
lake exe fir-wasm-artifact resident-platform \
  "$first/resident/platform.wasm"
lake exe fir-wasm-artifact resident-platform \
  "$second/resident/platform.wasm"
cmp "$first/resident/platform.wasm" "$second/resident/platform.wasm"
cmp "$first/resident/platform.wasm.json" \
  "$second/resident/platform.wasm.json"
lake exe fir-wasm-artifact resident-string \
  "$first/resident/string.wasm"
lake exe fir-wasm-artifact resident-string \
  "$second/resident/string.wasm"
cmp "$first/resident/string.wasm" "$second/resident/string.wasm"
cmp "$first/resident/string.wasm.json" \
  "$second/resident/string.wasm.json"
lake exe fir-wasm-artifact resident-fallbacks \
  "$first/resident/fallbacks.wasm"
lake exe fir-wasm-artifact resident-fallbacks \
  "$second/resident/fallbacks.wasm"
cmp "$first/resident/fallbacks.wasm" "$second/resident/fallbacks.wasm"
cmp "$first/resident/fallbacks.wasm.json" \
  "$second/resident/fallbacks.wasm.json"
lake -d .. env lean --run ../FirWasmOracleMain.lean all "$first"
lake -d .. env lean --run ../FirWasmOracleMain.lean all "$second"

for manifest in "$first"/*.wasm.json; do
  name="$(basename "$manifest" .wasm.json)"
  cmp "$first/$name.wasm" "$second/$name.wasm"
  cmp "$first/$name.wasm.json" "$second/$name.wasm.json"
  cmp "$first/$name.expected.json" "$second/$name.expected.json"
done

node concrete-readiness.mjs \
  "$first" _build ../W6-COVERAGE.md "$first/concrete-readiness.json" \
  --require-artifact-ready
node concrete-readiness.mjs \
  "$second" _build ../W6-COVERAGE.md "$second/concrete-readiness.json" \
  --require-artifact-ready
cmp "$first/concrete-readiness.json" "$second/concrete-readiness.json"
node test-concrete-readiness.mjs "$first/concrete-readiness.json"

node run-artifacts.mjs "$first"
node run-concrete-artifacts.mjs "$first"
if [[ -n "${FIR_BROWSER:-}" ]]; then
  concrete_corpus="_build/concrete-corpus"
  rm -rf "$concrete_corpus"
  mkdir -p "$concrete_corpus"
  cp "$first"/*.wasm "$first"/*.wasm.json "$first"/*.expected.json \
    "$concrete_corpus/"
  ./browser-concrete-check.sh "$FIR_BROWSER" "$concrete_corpus"
fi
