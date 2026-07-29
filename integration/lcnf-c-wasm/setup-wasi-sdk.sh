#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

for tool in curl sha256sum tar; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required setup tool not found: $tool" >&2
    exit 1
  fi
done

read -r asset expected_sha256 < <(fir_lcnf_c_wasi_sdk_asset)
archive="$deps_root/$asset"
sdk_dir="$deps_root/${asset%.tar.gz}"
download_url="https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-$FIR_LCNF_C_WASI_SDK_RELEASE/$asset"

mkdir -p "$deps_root"

if [[ ! -f "$archive" ]]; then
  curl \
    --fail \
    --location \
    --retry 3 \
    --output "$archive" \
    "$download_url"
fi

printf '%s  %s\n' "$expected_sha256" "$archive" | sha256sum --check -

if [[ ! -x "$sdk_dir/bin/clang" ]]; then
  tar -xzf "$archive" -C "$deps_root"
fi

if [[ ! -x "$sdk_dir/bin/clang" ]]; then
  echo "wasi-sdk archive did not create expected directory: $sdk_dir" >&2
  exit 1
fi

printf 'wasi-sdk %s is ready in %s\n' \
  "$FIR_LCNF_C_WASI_SDK_VERSION" \
  "$sdk_dir"
