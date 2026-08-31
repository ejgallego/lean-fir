#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
fir_root=$(cd "$here/../.." && pwd)
cd "$here"

export LAKE_CACHE_DIR="$(bash "$fir_root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true
export TMPDIR="$fir_root/.deps/tmp/vbp-manifest-resolver"
mkdir -p "$TMPDIR"

vbp_root=${VBP_ROOT:-$fir_root/.deps/source-views/vbp-manifest-resolver-1af64db2}
VBP_ROOT="$vbp_root" node package.mjs
package=$(realpath _build/vbp-manifest-resolver-current)
VBP_ROOT="$vbp_root" node package.mjs
test "$package" = "$(realpath _build/vbp-manifest-resolver-current)"

(
  cd "$package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)

echo "VBP manifest resolver package: $package"
