#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
build=true
if [[ "${1:-}" == "--no-build" ]]; then
  build=false
  shift
fi
out="${1:-$here/_build/prettyM-current}"
source_artifact="$here/_build/source-pretty-format-module.wasm"

if [[ "$build" == true ]]; then
  lake -d "$root" build Fir.Wasm.Emit.SourceExamples Fir.Wasm.Emit.Command
  (
    cd "$here"
    lake -d "$root" env lean FirWasmSourceExample.lean
  )
fi

test -s "$source_artifact"
test -s "$source_artifact.json"
test -s "$source_artifact.lcnf"

mkdir -p "$out/runtime/integration/talos/artifact" "$out/runtime/scripts"

install -m 0644 "$source_artifact" "$out/prettyM.wasm"
install -m 0644 "$source_artifact.json" "$out/prettyM.wasm.json"
install -m 0644 "$source_artifact.lcnf" "$out/prettyM.wasm.lcnf"
install -m 0644 "$here/prettyM-package/README.md" "$out/README.md"
install -m 0644 "$here/prettyM-package/smoke.mjs" "$out/smoke.mjs"

runtime_files=(
  artifact-external-registry.mjs
  check-concrete-pretty-format-module.mjs
  concrete-artifact-external-registry.mjs
  concrete-format-external-registry.mjs
  concrete-host.mjs
  module-client.mjs
)
for file in "${runtime_files[@]}"; do
  install -m 0644 "$here/$file" \
    "$out/runtime/integration/talos/artifact/$file"
done
install -m 0644 "$root/scripts/wasm_assert.mjs" \
  "$out/runtime/scripts/wasm_assert.mjs"
install -m 0644 "$root/scripts/wasm_format_external_algorithms.mjs" \
  "$out/runtime/scripts/wasm_format_external_algorithms.mjs"

(
  cd "$out"
  sha256sum \
    prettyM.wasm \
    prettyM.wasm.json \
    prettyM.wasm.lcnf \
    smoke.mjs \
    runtime/integration/talos/artifact/*.mjs \
    runtime/scripts/*.mjs > SHA256SUMS
)

node --input-type=module - "$out" "$root" <<'NODE'
import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const [out, root] = process.argv.slice(2);
const bytes = fs.readFileSync(path.join(out, "prettyM.wasm"));
const manifest = JSON.parse(
  fs.readFileSync(path.join(out, "prettyM.wasm.json"), "utf8"));
const module = new WebAssembly.Module(bytes);
const build = {
  format: "fir-prettyM-current-v1",
  sourceCommit: execFileSync(
    "git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
  artifact: {
    file: "prettyM.wasm",
    bytes: bytes.length,
    sha256: createHash("sha256").update(bytes).digest("hex"),
  },
  entry: manifest.entry,
  params: manifest.params,
  result: manifest.result,
  functionImports: WebAssembly.Module.imports(module)
    .filter((item) => item.kind === "function").length,
  memoryImports: WebAssembly.Module.imports(module)
    .filter((item) => item.kind === "memory").length,
  memoryExports: WebAssembly.Module.exports(module)
    .filter((item) => item.kind === "memory").length,
  runtime: "concrete JavaScript wasm32-lean64 host",
  test: "node smoke.mjs",
};
fs.writeFileSync(
  path.join(out, "BUILD.json"),
  `${JSON.stringify(build, null, 2)}\n`,
);
NODE

(
  cd "$out"
  sha256sum -c SHA256SUMS
  node smoke.mjs
)

printf 'prepared tested prettyM package: %s\n' "$out"
