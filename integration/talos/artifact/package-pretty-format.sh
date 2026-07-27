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
source_artifact="$here/_build/source-pretty-format-trace-resident-increments.wasm"

if [[ "$build" == true ]]; then
  lake -d "$root" build Fir.Wasm.Emit.ResidentPrettyFormat
  (
    cd "$here"
    lake -d "$root" env lean FirWasmPrettyTraceExample.lean
  )
fi

test -s "$source_artifact"
test -s "$source_artifact.json"
test -s "$source_artifact.lcnf"

out_parent="$(dirname "$out")"
out_name="$(basename "$out")"
mkdir -p "$out_parent"
out_parent="$(cd "$out_parent" && pwd)"
out="$out_parent/$out_name"
release_root="$out_parent/${out_name}-releases"
mkdir -p "$release_root"

stage="$(mktemp -d "$release_root/.stage.XXXXXX")"
link_tmp=""
legacy=""
cleanup() {
  if [[ -n "$link_tmp" ]]; then
    rm -f "$link_tmp"
  fi
  if [[ -n "$stage" ]]; then
    rm -rf "$stage"
  fi
  if [[ -n "$legacy" && ! -e "$out" ]]; then
    mv "$legacy" "$out"
    legacy=""
  fi
  if [[ -n "$legacy" ]]; then
    rm -rf "$legacy"
  fi
}
trap cleanup EXIT

mkdir -p \
  "$stage/runtime/integration/talos/artifact" \
  "$stage/runtime/scripts"

install -m 0644 "$source_artifact" "$stage/prettyM.wasm"
install -m 0644 "$source_artifact.json" "$stage/prettyM.wasm.json"
install -m 0644 "$source_artifact.lcnf" "$stage/prettyM.wasm.lcnf"
install -m 0644 "$here/prettyM-package/README.md" "$stage/README.md"
install -m 0644 "$here/prettyM-package/smoke.mjs" "$stage/smoke.mjs"

runtime_files=(
  artifact-external-registry.mjs
  check-concrete-pretty-format-module.mjs
  concrete-artifact-external-registry.mjs
  concrete-format-external-registry.mjs
  concrete-host.mjs
  check-concrete-pretty-format-trace-module.mjs
  module-client.mjs
)
for file in "${runtime_files[@]}"; do
  install -m 0644 "$here/$file" \
    "$stage/runtime/integration/talos/artifact/$file"
done
install -m 0644 "$root/scripts/wasm_assert.mjs" \
  "$stage/runtime/scripts/wasm_assert.mjs"
install -m 0644 "$root/scripts/wasm_format_external_algorithms.mjs" \
  "$stage/runtime/scripts/wasm_format_external_algorithms.mjs"

node --input-type=module - "$stage" "$root" <<'NODE'
import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const [out, root] = process.argv.slice(2);
const bytes = fs.readFileSync(path.join(out, "prettyM.wasm"));
const manifest = JSON.parse(
  fs.readFileSync(path.join(out, "prettyM.wasm.json"), "utf8"));
const module = new WebAssembly.Module(bytes);
const imports = WebAssembly.Module.imports(module);
const exports = WebAssembly.Module.exports(module);
const functionImports = imports.filter((item) => item.kind === "function").length;
const memoryImports = imports.filter((item) => item.kind === "memory").length;
const memoryExports = exports.filter((item) => item.kind === "memory").length;
if (memoryImports !== 0 || memoryExports !== 1) {
  throw new Error(
    `prettyM package requires module-owned memory; got ${memoryImports} imports and ${memoryExports} exports`);
}
const build = {
  format: "fir-prettyM-package-metadata-v2",
  sourceCommit: execFileSync(
    "git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
  sourceDirty: execFileSync(
    "git", ["status", "--porcelain"], { cwd: root, encoding: "utf8" }).trim() !== "",
  artifact: {
    file: "prettyM.wasm",
    bytes: bytes.length,
    sha256: createHash("sha256").update(bytes).digest("hex"),
  },
  entry: manifest.entry,
  params: manifest.params,
  result: manifest.result,
  functionImports,
  memoryImports,
  memoryExports,
  compatibility: {
    status: "experimental-unversioned",
    abiVersion: null,
  },
  capabilities: {
    representation: "wasm32-lean64",
    memoryOwner: "module",
    frontierProtocol: {
      status: "experimental",
      policy: "shared-monotone-frontier",
      read: "fir_heap_frontier",
      advance: "fir_heap_set_frontier",
      allocate: "fir_heap_alloc",
      heapBase: 1024,
      alignment: 8,
    },
    functionImportCount: functionImports,
    output: {
      semantic: "PrettyTrace",
      physical: manifest.result,
      textProjection: "String",
      styling: "MonadPrettyFormat event stream",
      taggedSegments: true,
    },
  },
  runtime: "Wasm-resident allocator/raw stores/constructors/immediate Naturals/closure allocations/setters/nonrecursive increments plus concrete JavaScript wasm32-lean64 handlers",
  test: "node smoke.mjs",
};
fs.writeFileSync(
  path.join(out, "BUILD.json"),
  `${JSON.stringify(build, null, 2)}\n`,
);
NODE

(
  cd "$stage"
  LC_ALL=C sha256sum \
    BUILD.json \
    README.md \
    prettyM.wasm \
    prettyM.wasm.json \
    prettyM.wasm.lcnf \
    smoke.mjs \
    runtime/integration/talos/artifact/*.mjs \
    runtime/scripts/*.mjs > SHA256SUMS
  sha256sum -c SHA256SUMS
  node smoke.mjs
)

source_commit="$(git -C "$root" rev-parse --short=12 HEAD)"
package_hash="$(sha256sum "$stage/SHA256SUMS" | awk '{ print $1 }')"
release_id="${source_commit}-${package_hash:0:16}"
release="$release_root/$release_id"
if [[ -e "$release" ]]; then
  cmp "$stage/SHA256SUMS" "$release/SHA256SUMS"
  rm -rf "$stage"
else
  mv "$stage" "$release"
fi
stage=""

link_tmp="$out_parent/.${out_name}.link.$$"
ln -s "${out_name}-releases/$release_id" "$link_tmp"

# Convert a legacy materialized output once. Subsequent publications replace
# the canonical symlink with one rename, so readers see one complete release
# or the other and never a partially copied package.
if [[ -e "$out" && ! -L "$out" ]]; then
  legacy="$release_root/.legacy.$$"
  mv "$out" "$legacy"
fi
mv -Tf "$link_tmp" "$out"
link_tmp=""
if [[ -n "$legacy" ]]; then
  rm -rf "$legacy"
  legacy=""
fi

printf 'prepared tested prettyM package: %s -> %s\n' "$out" "$release"
