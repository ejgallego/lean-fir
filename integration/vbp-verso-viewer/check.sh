#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
fir_root=$(cd "$here/../.." && pwd)
cd "$here"

export LAKE_CACHE_DIR="$(bash "$fir_root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true
export TMPDIR="$fir_root/.deps/tmp/vbp-verso-viewer"
mkdir -p "$TMPDIR"

vbp_root=${VBP_ROOT:-$fir_root/.deps/source-views/vbp-widget-cad90a2f}
vir_root=${VIR_ROOT:-$fir_root/.deps/source-views/vir-generic-90aa3f49}

node --check vbp-verso-viewer-browser-adapter.mjs
node --check package-policy.mjs
node --check package-smoke.mjs
node --check package.mjs

VBP_ROOT="$vbp_root" VIR_ROOT="$vir_root" node package.mjs
package=$(realpath _build/vbp-verso-viewer-current)
VBP_ROOT="$vbp_root" VIR_ROOT="$vir_root" node package.mjs
test "$package" = "$(realpath _build/vbp-verso-viewer-current)"

(
  cd "$package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)

echo "VBP FIR-native Verso viewer package: $package"
