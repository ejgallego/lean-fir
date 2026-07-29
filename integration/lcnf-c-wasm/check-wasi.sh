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

mkdir -p "$out_dir"

lean_prefix="$(lake env lean --print-prefix)"
generated_c="$out_dir/Smoke.c"
artifact="$out_dir/Smoke.wasm"

lake env lean \
  -c "$generated_c" \
  -R "$lane_dir" \
  "$lane_dir/Smoke.lean"

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
  -I "$lean_prefix/include"
)
link_flags=(
  "-Wl,--export=fir_lcnf_c_affine"
  "-Wl,--export=fir_lcnf_c_mix"
  "-Wl,--export=fir_lcnf_c_wasi_monotonic_ns"
  "-Wl,--gc-sections"
  "-Wl,--strip-all"
  "-Wl,--lto-O3"
)

"$wasi_clang" \
  "${compile_flags[@]}" \
  "$generated_c" \
  "$lane_dir/runtime/scalar.c" \
  "$lane_dir/runtime/wasi.c" \
  "${link_flags[@]}" \
  -o "$artifact"

NODE_NO_WARNINGS=1 node "$lane_dir/check-wasi.mjs" "$artifact"
sha256sum "$artifact"
