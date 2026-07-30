#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"
out_dir="${FIR_LCNF_C_WASM_WASI_OUT:-$repo_root/_build/lcnf-c-wasm/wasi}"

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

read -r asset _ < <(fir_lcnf_c_wasi_sdk_asset)
wasi_sdk="$deps_root/${asset%.tar.gz}"
wasi_clang="$wasi_sdk/bin/clang"

if [[ ! -x "$wasi_clang" ]]; then
  echo "wasi-sdk is not ready; run $lane_dir/setup-wasi-sdk.sh" >&2
  exit 1
fi

for tool in cc node; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required WASI check tool not found: $tool" >&2
    exit 1
  fi
done

lean_version="$(lake env lean --version)"
if [[ "$lean_version" != *"commit $FIR_LCNF_C_LEAN_COMMIT"* ]]; then
  echo "Lean compiler does not match the pinned WASI ABI: $lean_version" >&2
  exit 1
fi

mkdir -p "$out_dir"

lean_prefix="$(lake env lean --print-prefix)"
generated_scalar_c="$out_dir/Smoke.c"
generated_heap_c="$out_dir/HeapSmoke.c"
generated_core_c="$out_dir/WasiCoreSmoke.c"
native_heap_generated_o="$out_dir/HeapSmoke.native.o"
native_heap_host_o="$out_dir/native_heap.o"
native_heap_executable="$out_dir/HeapSmoke.native"
native_heap_results="$out_dir/HeapSmoke.native.txt"
native_core_generated_o="$out_dir/WasiCoreSmoke.native.o"
native_core_host_o="$out_dir/native_wasi_core.o"
native_core_executable="$out_dir/WasiCoreSmoke.native"
native_core_results="$out_dir/WasiCoreSmoke.native.txt"
artifact="$out_dir/WasiCoreSmoke.wasm"

lake env lean \
  -c "$generated_scalar_c" \
  -R "$lane_dir" \
  "$lane_dir/Smoke.lean"

lake env lean \
  -c "$generated_heap_c" \
  -R "$lane_dir" \
  "$lane_dir/HeapSmoke.lean"

lake env lean \
  -c "$generated_core_c" \
  -R "$lane_dir" \
  "$lane_dir/WasiCoreSmoke.lean"

if ! grep -q "lean_alloc_ctor" "$generated_heap_c"; then
  echo "WASI heap fixture no longer contains a Lean constructor allocation" >&2
  exit 1
fi

for symbol in \
  lean_alloc_closure \
  lean_apply_1 \
  lean_array_push \
  lean_string_append; do
  if ! grep -q "$symbol" "$generated_core_c"; then
    echo "WASI core fixture no longer references $symbol" >&2
    exit 1
  fi
done

lake env leanc \
  -O3 \
  -DNDEBUG \
  -flto \
  -fomit-frame-pointer \
  -ffp-contract=off \
  -c "$generated_heap_c" \
  -o "$native_heap_generated_o"
cc \
  -O3 \
  -DNDEBUG \
  -fomit-frame-pointer \
  -ffp-contract=off \
  -c "$lane_dir/runtime/native_heap.c" \
  -o "$native_heap_host_o"
lake env leanc \
  -O3 \
  -flto \
  "$native_heap_generated_o" \
  "$native_heap_host_o" \
  -o "$native_heap_executable"
"$native_heap_executable" > "$native_heap_results"

lake env leanc \
  -O3 \
  -DNDEBUG \
  -flto \
  -fomit-frame-pointer \
  -ffp-contract=off \
  -c "$generated_core_c" \
  -o "$native_core_generated_o"
cc \
  -O3 \
  -DNDEBUG \
  -fomit-frame-pointer \
  -ffp-contract=off \
  -c "$lane_dir/runtime/native_wasi_core.c" \
  -o "$native_core_host_o"
lake env leanc \
  -O3 \
  -flto \
  "$native_core_generated_o" \
  "$native_core_host_o" \
  -o "$native_core_executable"
"$native_core_executable" > "$native_core_results"

compile_flags=(
  --target=wasm32-wasip1
  -mexec-model=reactor
  -std=c11
  -O3
  -DNDEBUG
  -DLEAN_EXPORTING
  -flto=full
  -fomit-frame-pointer
  -ffunction-sections
  -fdata-sections
  -fvisibility=hidden
  -fno-exceptions
  -fno-unwind-tables
  -fno-asynchronous-unwind-tables
  -fno-fast-math
  -ffp-contract=off
  -I "$lane_dir/runtime/wasi-include"
  -I "$lean_prefix/include"
)
link_flags=(
  "-Wl,--export=fir_lcnf_c_affine"
  "-Wl,--export=fir_lcnf_c_mix"
  "-Wl,--export=fir_lcnf_c_wasi_monotonic_ns"
  "-Wl,--export=fir_lcnf_c_heap_checksum"
  "-Wl,--export=fir_lcnf_c_wasi_core_checksum"
  "-Wl,--export=fir_lcnf_c_wasi_runtime_abi"
  "-Wl,--export=fir_lcnf_c_wasi_allocations"
  "-Wl,--export=fir_lcnf_c_wasi_deallocations"
  "-Wl,--export=fir_lcnf_c_wasi_live_objects"
  "-Wl,--export=fir_lcnf_c_wasi_peak_live_objects"
  "-Wl,--export=fir_lcnf_c_wasi_constructor_deallocations"
  "-Wl,--export=fir_lcnf_c_wasi_closure_deallocations"
  "-Wl,--export=fir_lcnf_c_wasi_array_deallocations"
  "-Wl,--export=fir_lcnf_c_wasi_string_deallocations"
  "-Wl,--gc-sections"
  "-Wl,--strip-all"
  "-Wl,--lto-O3"
)

"$wasi_clang" \
  "${compile_flags[@]}" \
  "$generated_scalar_c" \
  "$generated_heap_c" \
  "$generated_core_c" \
  "$lane_dir/runtime/scalar.c" \
  "$lane_dir/runtime/wasi.c" \
  "$lane_dir/runtime/wasi_core.c" \
  "${link_flags[@]}" \
  -o "$artifact"

NODE_NO_WARNINGS=1 node \
  "$lane_dir/check-wasi.mjs" \
  "$artifact" \
  "$native_heap_results" \
  "$native_core_results"
sha256sum "$artifact" "$native_heap_results" "$native_core_results"
