#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
out_dir="${1:-$lane_dir/_build/prettyM-emscripten-current}"
fir_package="${FIR_PRETTY_M_NATIVE_PACKAGE:-$repo_root/integration/talos/artifact/_build/prettyM-current}"

mkdir -p "$out_dir"

"$lane_dir/build-emscripten.sh" \
  --root "$lane_dir" \
  --out-dir "$out_dir" \
  --name prettyM \
  --extra-c-source "$lane_dir/runtime/prettyM-bridge.c" \
  --heap-view \
  --export fir_lcnf_c_pretty_input_alloc \
  --export fir_lcnf_c_pretty_render \
  --export fir_lcnf_c_pretty_result_ptr \
  --export fir_lcnf_c_pretty_result_len \
  --export fir_lcnf_c_pretty_release \
  "$lane_dir/PrettyM.lean"

install -m 0644 "$lane_dir/emscripten-loader.mjs" \
  "$out_dir/emscripten-loader.mjs"
install -m 0644 "$lane_dir/prettyM-emscripten-adapter.mjs" \
  "$out_dir/prettyM-emscripten-adapter.mjs"
install -m 0644 "$lane_dir/prettyM-emscripten-package/README.md" \
  "$out_dir/README.md"

if [[ ! -s "$fir_package/prettyM.wasm" ]]; then
  "$repo_root/integration/talos/artifact/package-pretty-format.sh" "$fir_package"
fi

node "$lane_dir/check-prettyM-differential.mjs" \
  "$out_dir/prettyM.manifest.json" \
  "$fir_package"

(
  cd "$out_dir"
  LC_ALL=C sha256sum \
    README.md \
    emscripten-loader.mjs \
    prettyM-emscripten-adapter.mjs \
    prettyM.manifest.json \
    prettyM.mjs \
    prettyM.wasm > SHA256SUMS
  sha256sum -c SHA256SUMS
)

printf 'prepared tested C/Emscripten prettyM package: %s\n' "$out_dir"
