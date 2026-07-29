#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"
out_dir="${FIR_LCNF_C_WASM_EMSCRIPTEN_OUT:-$repo_root/_build/lcnf-c-wasm/emscripten}"

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

for tool in cc node; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required Emscripten check tool not found: $tool" >&2
    exit 1
  fi
done

emsdk_dir="$deps_root/emsdk"
lean_build="$deps_root/lean4-emscripten-build"
lean_runtime="$lean_build/lib/lean/libleanrt.a"
lean_init="$lean_build/lib/lean/libInit.a"
lean_std="$lean_build/lib/lean/libStd.a"

for dependency in "$emsdk_dir/emsdk_env.sh" "$lean_runtime" "$lean_init" "$lean_std"; do
  if [[ ! -f "$dependency" ]]; then
    echo "Emscripten Lean runtime is not ready; run $lane_dir/setup-emscripten.sh" >&2
    exit 1
  fi
done

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
runtime_generated_c="$out_dir/RuntimeSmoke.c"
runtime_generated_o="$out_dir/RuntimeSmoke.o"
runtime_host_o="$out_dir/runtime.o"
native_generated_o="$out_dir/RuntimeSmoke.native.o"
native_host_o="$out_dir/native.o"
native_executable="$out_dir/RuntimeSmoke.native"
native_results="$out_dir/RuntimeSmoke.native.txt"
module="$out_dir/RuntimeSmoke.mjs"
artifact="$out_dir/RuntimeSmoke.wasm"

lake env lean \
  -c "$generated_c" \
  -R "$lane_dir" \
  "$lane_dir/HeapSmoke.lean"

lake env lean \
  -c "$runtime_generated_c" \
  -R "$lane_dir" \
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
  -sMODULARIZE=1
  -sWASM_BIGINT=1
  "-sEXPORTED_FUNCTIONS=_fir_lcnf_c_heap_checksum,_fir_lcnf_c_runtime_checksum,_fir_lcnf_c_runtime_initialize"
)

emcc "${compile_flags[@]}" -c "$generated_c" -o "$generated_o"
emcc \
  "${compile_flags[@]}" \
  -c "$runtime_generated_c" \
  -o "$runtime_generated_o"
emcc \
  "${compile_flags[@]}" \
  -c "$lane_dir/runtime/emscripten.c" \
  -o "$runtime_host_o"
em++ \
  "$generated_o" \
  "$runtime_generated_o" \
  "$runtime_host_o" \
  "-Wl,--start-group" \
  "$lean_std" \
  "$lean_init" \
  "$lean_runtime" \
  "-Wl,--end-group" \
  "${link_flags[@]}" \
  -o "$module"

node \
  "$lane_dir/check-emscripten.mjs" \
  "$module" \
  "$artifact" \
  "$native_results"
if [[ -n "${FIR_BROWSER:-}" ]]; then
  "$lane_dir/check-emscripten-browser.sh" "$FIR_BROWSER"
fi
sha256sum "$module" "$artifact" "$native_results"
