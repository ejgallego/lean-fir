#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
declare -a build_options=()
if [[ "${1:-}" == "--rebuild" ]]; then
  build_options+=(--rebuild)
  shift
fi
package_current="${1:-$lane_dir/_build/prettyM-emscripten-package-current}"
if (($# > 1)); then
  echo "usage: package-prettyM-emscripten.sh [--rebuild] [package-current-link]" >&2
  exit 1
fi
fir_package="$repo_root/integration/talos/artifact/_build/prettyM-current"
build_dir="$repo_root/.deps/lcnf-c-wasm/prettyM-package-build"

if [[ -n "${FIR_PRETTY_M_NATIVE_PACKAGE:-}" ]]; then
  echo "FIR_PRETTY_M_NATIVE_PACKAGE is no longer supported: the differential gate builds its comparator from this FIR tree" >&2
  exit 1
fi

mkdir -p "$build_dir"

"$lane_dir/build-emscripten.sh" \
  "${build_options[@]}" \
  --root "$lane_dir" \
  --out-dir "$build_dir" \
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
  "$build_dir/emscripten-loader.mjs"
install -m 0644 "$lane_dir/prettyM-emscripten-adapter.mjs" \
  "$build_dir/prettyM-emscripten-adapter.mjs"
install -m 0644 "$lane_dir/prettyM-emscripten-package/README.md" \
  "$build_dir/README.md"
install -m 0644 "$lane_dir/prettyM-emscripten-package/smoke.mjs" \
  "$build_dir/smoke.mjs"

"$repo_root/integration/talos/artifact/package-pretty-format.sh" "$fir_package"
(
  cd "$fir_package"
  sha256sum -c SHA256SUMS
)
node "$lane_dir/check-current-prettyM-comparator.mjs" \
  "$fir_package/BUILD.json" "$repo_root"

node "$lane_dir/check-prettyM-differential.mjs" \
  "$build_dir/prettyM.manifest.json" \
  "$fir_package"

node "$lane_dir/publish-prettyM-emscripten.mjs" \
  "$build_dir" "$package_current" "$repo_root" "$fir_package/BUILD.json"
node "$lane_dir/test-immutable-prettyM-package.mjs" \
  "$build_dir" "$repo_root"

printf 'prepared tested immutable C/Emscripten prettyM package: %s\n' \
  "$package_current"
