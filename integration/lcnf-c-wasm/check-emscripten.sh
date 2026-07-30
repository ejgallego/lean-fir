#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
out_dir="${FIR_LCNF_C_WASM_EMSCRIPTEN_OUT:-$repo_root/_build/lcnf-c-wasm/emscripten}"

for tool in cc node; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required Emscripten check tool not found: $tool" >&2
    exit 1
  fi
done

mkdir -p "$out_dir"

node "$lane_dir/test-benchmark-report.mjs"

generated_c="$out_dir/HeapSmoke.c"
runtime_generated_c="$out_dir/RuntimeSmoke.c"
native_generated_o="$out_dir/RuntimeSmoke.native.o"
native_host_o="$out_dir/native.o"
native_executable="$out_dir/RuntimeSmoke.native"
native_results="$out_dir/RuntimeSmoke.native.txt"
module="$out_dir/RuntimeSmoke.mjs"
artifact="$out_dir/RuntimeSmoke.wasm"
manifest="$out_dir/RuntimeSmoke.manifest.json"

"$lane_dir/build-emscripten.sh" \
  --root "$lane_dir" \
  --out-dir "$out_dir" \
  --name RuntimeSmoke \
  --extra-source "$lane_dir/HeapSmoke.lean" \
  --export fir_lcnf_c_heap_checksum \
  --export fir_lcnf_c_runtime_checksum \
  --start fir_lcnf_c_runtime_probe \
  "$lane_dir/RuntimeSmoke.lean"

if ! grep -q "lean_alloc_ctor" "$generated_c"; then
  echo "heap fixture no longer contains a Lean constructor allocation" >&2
  exit 1
fi
if ! grep -q "initialize_Std_Data_HashMap" "$runtime_generated_c"; then
  echo "runtime fixture no longer imports the pinned Std archive" >&2
  exit 1
fi
if ! grep -q "lean_alloc_closure" "$runtime_generated_c"; then
  echo "runtime fixture no longer allocates a captured Lean closure" >&2
  exit 1
fi

lean_prefix="$(lake env lean --print-prefix)"
lake env leanc \
  -O3 \
  -DNDEBUG \
  -flto \
  -fomit-frame-pointer \
  -ffp-contract=off \
  -c "$runtime_generated_c" \
  -o "$native_generated_o"
cc \
  -O3 \
  -DNDEBUG \
  -fomit-frame-pointer \
  -ffp-contract=off \
  -I "$lean_prefix/include" \
  -c "$lane_dir/runtime/native.c" \
  -o "$native_host_o"
lake env leanc \
  -O3 \
  -flto \
  "$native_generated_o" \
  "$native_host_o" \
  -o "$native_executable"
"$native_executable" > "$native_results"

node \
  "$lane_dir/check-emscripten.mjs" \
  "$manifest" \
  "$native_results"
if [[ -n "${FIR_BROWSER:-}" ]]; then
  "$lane_dir/check-emscripten-browser.sh" "$FIR_BROWSER"
fi
sha256sum "$module" "$artifact" "$manifest" "$native_results"
