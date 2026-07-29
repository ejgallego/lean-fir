#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
out_dir="${FIR_LCNF_C_WASM_OUT:-$repo_root/_build/lcnf-c-wasm}"

resolve_tool() {
  local override="$1"
  shift
  if [[ -n "$override" ]]; then
    if [[ ! -x "$override" ]]; then
      echo "tool is not executable: $override" >&2
      return 1
    fi
    printf '%s\n' "$override"
    return
  fi

  local candidate
  for candidate in "$@"; do
    if [[ "$candidate" == */* ]]; then
      if [[ -x "$candidate" ]]; then
        printf '%s\n' "$candidate"
        return
      fi
    elif command -v "$candidate" >/dev/null 2>&1; then
      command -v "$candidate"
      return
    fi
  done

  return 1
}

local_lld_18="$repo_root/.deps/lld-18/usr/lib/llvm-18/bin/wasm-ld"
lane_lld_18="$repo_root/.deps/lcnf-c-wasm/lld/usr/lib/llvm-18/bin/wasm-ld"
wasm_ld="$(
  resolve_tool "${FIR_WASM_LD:-}" \
    wasm-ld-18 wasm-ld "$lane_lld_18" "$local_lld_18"
)" || {
  echo "wasm-ld not found; run $lane_dir/setup-lld-debian.sh or set FIR_WASM_LD" >&2
  exit 1
}

if [[ "$(basename "$wasm_ld")" == *18* || "$wasm_ld" == *llvm-18* ]]; then
  default_clang_candidates=(clang-18 clang)
else
  default_clang_candidates=(clang)
fi
wasm_clang="$(
  resolve_tool "${FIR_WASM_CLANG:-}" "${default_clang_candidates[@]}"
)" || {
  echo "clang with the WebAssembly target is required; set FIR_WASM_CLANG" >&2
  exit 1
}

mkdir -p "$out_dir"

lean_prefix="$(lake env lean --print-prefix)"
generated_c="$out_dir/Smoke.c"
artifact="$out_dir/Smoke.wasm"

lake env lean \
  -c "$generated_c" \
  -R "$lane_dir" \
  "$lane_dir/Smoke.lean"

compile_flags=(
  --target=wasm32-unknown-unknown
  "-fuse-ld=$wasm_ld"
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
  -nostdlib
  -I "$lean_prefix/include"
)
link_flags=(
  "-Wl,--no-entry"
  "-Wl,--export=fir_lcnf_c_affine"
  "-Wl,--export=fir_lcnf_c_mix"
  "-Wl,--gc-sections"
  "-Wl,--strip-all"
  "-Wl,--lto-O3"
)

"$wasm_clang" \
  "${compile_flags[@]}" \
  "$generated_c" \
  "$lane_dir/runtime/scalar.c" \
  "${link_flags[@]}" \
  -o "$artifact"

node "$lane_dir/check.mjs" "$artifact"
sha256sum "$artifact"
