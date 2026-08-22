#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
out_dir="${FIR_LCNF_C_WASM_UNTHREADED_OUT:-$repo_root/_build/lcnf-c-wasm/emscripten-unthreaded}"

mkdir -p "$out_dir"

"$lane_dir/build-emscripten.sh" \
  --runtime-profile unthreaded \
  --root "$lane_dir" \
  --out-dir "$out_dir" \
  --name Smoke \
  --heap-view \
  --export fir_lcnf_c_affine \
  --export fir_lcnf_c_mix \
  "$lane_dir/Smoke.lean"

node "$lane_dir/check-emscripten-unthreaded.mjs" \
  "$out_dir/Smoke.manifest.json"

