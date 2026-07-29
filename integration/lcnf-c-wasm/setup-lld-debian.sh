#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_dir="$repo_root/.deps/lcnf-c-wasm"
deb_dir="$deps_dir/deb"
install_dir="$deps_dir/lld"
package="${FIR_LLD_DEBIAN_PACKAGE:-lld-18}"

mkdir -p "$deb_dir" "$install_dir"

(
  cd "$deb_dir"
  apt-get download "$package"
)

mapfile -t packages < <(
  find "$deb_dir" -maxdepth 1 -type f -name "${package}_*.deb" -print |
    sort
)
if [[ "${#packages[@]}" -eq 0 ]]; then
  echo "apt-get did not produce a ${package} package" >&2
  exit 1
fi

package_file="${packages[${#packages[@]} - 1]}"
dpkg-deb -x "$package_file" "$install_dir"

mapfile -t linkers < <(
  find "$install_dir" -type f -name lld -path '*/llvm-*/bin/lld' -print |
    sort
)
if [[ "${#linkers[@]}" -eq 0 ]]; then
  echo "the extracted package does not contain lld" >&2
  exit 1
fi

linker="${linkers[${#linkers[@]} - 1]}"
wasm_ld="$(dirname "$linker")/wasm-ld"
if [[ ! -x "$wasm_ld" ]]; then
  echo "the extracted package does not expose wasm-ld" >&2
  exit 1
fi

"$wasm_ld" --version
printf 'FIR_WASM_LD=%s\n' "$wasm_ld"
