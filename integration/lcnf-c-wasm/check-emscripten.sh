#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"
out_dir="${FIR_LCNF_C_WASM_EMSCRIPTEN_OUT:-$repo_root/_build/lcnf-c-wasm/emscripten}"

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

emsdk_dir="$deps_root/emsdk"
lean_build="$deps_root/lean4-emscripten-build"
lean_runtime="$lean_build/lib/lean/libleanrt.a"

if [[ ! -f "$emsdk_dir/emsdk_env.sh" || ! -f "$lean_runtime" ]]; then
  echo "Emscripten Lean runtime is not ready; run $lane_dir/setup-emscripten.sh" >&2
  exit 1
fi

lean_version="$(lake env lean --version)"
if [[ "$lean_version" != *"commit $FIR_LCNF_C_LEAN_COMMIT"* ]]; then
  echo "Lean compiler does not match the pinned runtime: $lean_version" >&2
  exit 1
fi

export EMSDK_QUIET=1
# shellcheck disable=SC1091
source "$emsdk_dir/emsdk_env.sh"

if [[ "$(emcc --version | head -n 1)" != *"$FIR_LCNF_C_EMSDK_VERSION"* ]]; then
  echo "active Emscripten does not match pin $FIR_LCNF_C_EMSDK_VERSION" >&2
  exit 1
fi

mkdir -p "$out_dir"

generated_c="$out_dir/HeapSmoke.c"
generated_o="$out_dir/HeapSmoke.o"
runtime_o="$out_dir/runtime.o"
module="$out_dir/HeapSmoke.mjs"
artifact="$out_dir/HeapSmoke.wasm"

lake env lean \
  -c "$generated_c" \
  -R "$lane_dir" \
  "$lane_dir/HeapSmoke.lean"

if ! grep -q "lean_alloc_ctor" "$generated_c"; then
  echo "heap fixture no longer contains a Lean constructor allocation" >&2
  exit 1
fi

compile_flags=(
  -std=c11
  -O3
  -DNDEBUG
  -DLEAN_EXPORTING
  -flto
  -fomit-frame-pointer
  -ffunction-sections
  -fdata-sections
  -fvisibility=hidden
  -fno-fast-math
  -ffp-contract=off
  -fwasm-exceptions
  -pthread
  -I "$lean_build/include"
)
link_flags=(
  -O3
  -flto
  -fwasm-exceptions
  -pthread
  --no-entry
  "-Wl,--gc-sections"
  "-Wl,--strip-all"
  -sALLOW_MEMORY_GROWTH=1
  -sASSERTIONS=0
  "-sENVIRONMENT=node,web"
  -sEXPORT_ES6=1
  -sFILESYSTEM=0
  -sMODULARIZE=1
  -sWASM_BIGINT=1
  -sEXPORTED_FUNCTIONS=_fir_lcnf_c_heap_checksum
)

emcc "${compile_flags[@]}" -c "$generated_c" -o "$generated_o"
emcc \
  "${compile_flags[@]}" \
  -c "$lane_dir/runtime/emscripten.c" \
  -o "$runtime_o"
em++ \
  "$generated_o" \
  "$runtime_o" \
  "$lean_runtime" \
  "${link_flags[@]}" \
  -o "$module"

node "$lane_dir/check-emscripten.mjs" "$module" "$artifact"
sha256sum "$module" "$artifact"
