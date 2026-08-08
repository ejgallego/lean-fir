#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
build=true
rebuild=false
while [[ "${1:-}" == --* ]]; do
  case "$1" in
    --no-build)
      build=false
      ;;
    --rebuild)
      rebuild=true
      ;;
    --help)
      cat <<'EOF'
usage: package-pretty-format.sh [--no-build | --rebuild] [output-directory]

  --no-build  Package the existing generated source artifact.
  --rebuild   Regenerate the source artifact even if its cache is valid.
EOF
      exit 0
      ;;
    *)
      echo "unsupported option: $1" >&2
      exit 1
      ;;
  esac
  shift
done
if [[ "$build" == false && "$rebuild" == true ]]; then
  echo "--no-build and --rebuild cannot be combined" >&2
  exit 1
fi
out="${1:-$here/_build/prettyM-current}"
if (($# > 1)); then
  echo "only one output directory may be specified" >&2
  exit 1
fi
source_artifact="$here/_build/source-pretty-format-trace-resident-closed.wasm"

file_digest() {
  local line
  line="$(sha256sum "$1")"
  printf '%s\n' "${line%% *}"
}

hash_key() {
  local line
  line="$(sha256sum)"
  printf '%s\n' "${line%% *}"
}

key_field() {
  printf '%s\0%s\0' "$1" "$2"
}

generator_cache_hit() {
  local expected_key="$1"
  local stored_key
  local index
  local actual_digest
  local -a outputs=(
    "$source_artifact"
    "$source_artifact.json"
    "$source_artifact.lcnf"
  )
  local -a stored_digests=()

  [[ "$rebuild" == false ]] || return 1
  [[ -f "$generator_cache_key" && -f "$generator_cache_digests" ]] || return 1
  IFS= read -r stored_key < "$generator_cache_key" || return 1
  [[ "$stored_key" == "$expected_key" ]] || return 1
  mapfile -t stored_digests < "$generator_cache_digests"
  ((${#stored_digests[@]} == ${#outputs[@]})) || return 1
  for index in "${!outputs[@]}"; do
    [[ "${stored_digests[index]}" =~ ^[0-9a-f]{64}$ ]] || return 1
    [[ -s "${outputs[index]}" ]] || return 1
    actual_digest="$(file_digest "${outputs[index]}")"
    [[ "$actual_digest" == "${stored_digests[index]}" ]] || return 1
  done
}

record_generator_cache() {
  local key="$1"
  local key_tmp
  local digests_tmp
  key_tmp="$(mktemp "$generator_cache_dir/.key.XXXXXX")"
  digests_tmp="$(mktemp "$generator_cache_dir/.digests.XXXXXX")"
  printf '%s\n' "$key" > "$key_tmp"
  file_digest "$source_artifact" > "$digests_tmp"
  file_digest "$source_artifact.json" >> "$digests_tmp"
  file_digest "$source_artifact.lcnf" >> "$digests_tmp"
  mv -f "$digests_tmp" "$generator_cache_digests"
  mv -f "$key_tmp" "$generator_cache_key"
}

if [[ "$build" == true ]]; then
  lake -d "$root" build Fir.Wasm.Emit.ResidentPrettyFormat
  generator_cache_dir="$here/_build/.fir-prettyM-cache"
  generator_cache_key="$generator_cache_dir/generator.key"
  generator_cache_digests="$generator_cache_dir/generator.digests"
  mkdir -p "$generator_cache_dir"
  generator_source="$here/FirWasmPrettyTraceExample.lean"
  lean_version="$(lake -d "$root" env lean --version)"
  lean_prefix="$(lake -d "$root" env lean --print-prefix)"
  lean_tool="$lean_prefix/bin/lean"
  lake_version="$(lake --version)"
  generator_dependency_list="$(
    lake -d "$root" env lean --deps "$generator_source"
  )"
  mapfile -t generator_dependencies <<< "$generator_dependency_list"
  generator_key="$({
    key_field cache-format fir-prettyM-source-v1
    key_field root "$root"
    key_field source "$generator_source"
    key_field source-sha256 "$(file_digest "$generator_source")"
    key_field lean "$lean_tool"
    key_field lean-sha256 "$(file_digest "$lean_tool")"
    key_field lean-version "$lean_version"
    key_field lake-version "$lake_version"
    key_field command "lake -d <root> env lean FirWasmPrettyTraceExample.lean"
    dependency_index=0
    for dependency in "${generator_dependencies[@]}"; do
      [[ -f "$dependency" ]] || {
        echo "Lean dependency does not exist: $dependency" >&2
        exit 1
      }
      key_field "dependency.$dependency_index.path" "$dependency"
      key_field "dependency.$dependency_index.sha256" "$(file_digest "$dependency")"
      trace="${dependency%.olean}.trace"
      if [[ -f "$trace" ]]; then
        key_field "dependency.$dependency_index.trace" "$trace"
        key_field "dependency.$dependency_index.trace-sha256" "$(file_digest "$trace")"
      fi
      dependency_index=$((dependency_index + 1))
    done
  } | hash_key)"
  if generator_cache_hit "$generator_key"; then
    printf 'HIT prettyM source artifact\n'
  else
    printf 'BUILD prettyM source artifact\n'
    (
      cd "$here"
      lake -d "$root" env lean FirWasmPrettyTraceExample.lean
    )
    test -s "$source_artifact"
    test -s "$source_artifact.json"
    test -s "$source_artifact.lcnf"
    record_generator_cache "$generator_key"
  fi
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
install -m 0644 "$here/prettyM-browser-adapter.mjs" \
  "$stage/prettyM-browser-adapter.mjs"
install -m 0644 "$here/check-prettyM-browser-adapter.mjs" \
  "$stage/check-prettyM-browser-adapter.mjs"

runtime_files=(
  check-concrete-pretty-format-module.mjs
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
install -m 0644 "$root/scripts/wasm_semantic_host.mjs" \
  "$stage/runtime/scripts/wasm_semantic_host.mjs"

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
if (imports.length !== 0 || functionImports !== 0) {
  throw new Error(
    `prettyM package must be self-contained; got ${imports.length} total imports and ${functionImports} function imports`);
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
    browserAdapter: {
      module: "prettyM-browser-adapter.mjs",
      apiVersion: "fir.prettyM.browser/v1",
      phases: ["prepare", "execute", "decode", "render"],
      timings: [
        "fetchMs",
        "compileMs",
        "instantiateMs",
        "normalizeMs",
        "allocateMs",
        "encodeMs",
        "prepareMs",
        "executeMs",
        "decodeMs",
        "totalMs",
      ],
    },
    inputLayout: {
      version: "lean-4.32-Std.Format.compact/v1",
      leanVersion: "4.32.0",
      representation: "compact-discriminated-union",
      constructors: [
        "nil",
        "line",
        "align",
        "text",
        "nest",
        "append",
        "group",
        "tag",
      ],
      naturalInput: [
        "bigint",
        "safe-integer",
        "canonical-unsigned-decimal-string",
      ],
      integerInput: [
        "bigint",
        "safe-integer",
        "canonical-signed-decimal-string",
      ],
      rawTarget: "Lean 4.32 Std.Format",
    },
    ownership: {
      version: "fir.prettyM.module-owned-transfer/v1",
      publicInput: "borrowed-immutable-javascript",
      encodedInput: "fresh-owned-lean-graph-transferred-to-entry",
      output: "decoded-javascript-copy",
      rawAddressesExposed: false,
      memoryOwner: "module",
      allocator: "single-bulk-resident-allocation-per-render",
      frontier: "monotone-resynchronized-before-and-after-each-phase",
      reclamation: "instance-lifetime-bump-arena",
    },
    output: {
      semantic: "PrettyTrace",
      physical: manifest.result,
      textProjection: "String",
      styling: "MonadPrettyFormat event stream",
      taggedSegments: true,
    },
  },
  runtime: "Self-contained Wasm-resident allocator/raw stores/constructors/immediate Naturals/closure allocations/setters/tag mutation/reference increments/recursive releases/delete/lazy-cache publication/arbitrary-precision Nat+Int/UTF-8 String operations/String literals/fail-closed fallbacks",
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
    prettyM-browser-adapter.mjs \
    check-prettyM-browser-adapter.mjs \
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
