#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
html_dir="$repo_root/integration/verso-html"
declare -a build_options=()
if [[ "${1:-}" == "--rebuild" ]]; then
  build_options+=(--rebuild)
  shift
fi
out_dir="${1:-$lane_dir/_build/prettyM-html-emscripten-current}"
if (($# > 1)); then
  echo "usage: package-prettyM-html-emscripten.sh [--rebuild] [output-directory]" >&2
  exit 1
fi

verso_root="$(realpath "${VERSO_ROOT:-$html_dir/.verso}")"
native_package="${FIR_PRETTY_M_NATIVE_HTML_PACKAGE:-$html_dir/_build/verso-html-current}"
generated_pretty="$html_dir/.lake/build/ir/VersoSlides/Pretty.c"

lake -d "$html_dir" --keep-toolchain --reconfigure \
  -KversoRoot="$verso_root" build VersoHtmlSource
test -s "$generated_pretty"
mkdir -p "$out_dir"

"$lane_dir/build-emscripten.sh" \
  "${build_options[@]}" \
  --root "$lane_dir" \
  --lake-root "$html_dir" \
  --manifest-root "$repo_root" \
  --out-dir "$out_dir" \
  --name prettyM-html \
  --extra-c-source "$generated_pretty" \
  --extra-c-source "$lane_dir/runtime/prettyM-html-package-shim.c" \
  --extra-c-source "$lane_dir/runtime/prettyM-html-bridge.c" \
  --heap-view \
  --export fir_lcnf_c_pretty_html_input_alloc \
  --export fir_lcnf_c_pretty_html_render \
  --export fir_lcnf_c_pretty_html_result_ptr \
  --export fir_lcnf_c_pretty_html_result_len \
  --export fir_lcnf_c_pretty_html_release \
  "$lane_dir/PrettyMHtml.lean"

install -m 0644 "$lane_dir/emscripten-loader.mjs" \
  "$out_dir/emscripten-loader.mjs"
install -m 0644 "$lane_dir/prettyM-emscripten-adapter.mjs" \
  "$out_dir/prettyM-emscripten-adapter.mjs"
install -m 0644 "$lane_dir/prettyM-html-emscripten-adapter.mjs" \
  "$out_dir/prettyM-html-emscripten-adapter.mjs"
install -m 0644 "$lane_dir/prettyM-html-emscripten-package/README.md" \
  "$out_dir/README.md"

node "$lane_dir/stamp-prettyM-html-manifest.mjs" \
  "$out_dir/prettyM-html.manifest.json" "$repo_root" "$verso_root"

if [[ ! -s "$native_package/prettyM.wasm" ]]; then
  VERSO_ROOT="$verso_root" bash "$html_dir/check.sh"
fi
node "$lane_dir/check-prettyM-html-differential.mjs" \
  "$out_dir/prettyM-html.manifest.json" "$native_package"

(
  cd "$out_dir"
  LC_ALL=C sha256sum \
    README.md \
    emscripten-loader.mjs \
    prettyM-emscripten-adapter.mjs \
    prettyM-html-emscripten-adapter.mjs \
    prettyM-html.manifest.json \
    prettyM-html.mjs \
    prettyM-html.wasm > SHA256SUMS
  sha256sum -c SHA256SUMS
)

printf 'prepared tested C/Emscripten prettyM HTML package: %s\n' "$out_dir"
