#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
fir_root=$(cd "$here/../.." && pwd)
bash "$here/build.sh"
package=$(realpath _build/illuminate-player-current)
selection_package=$(realpath _build/illuminate-selection-player-current)

# The build runs in a child shell; test commands also need local scratch and
# the same source path/cache for their independent native-oracle cone.
export TMPDIR="$fir_root/.deps/tmp/illuminate-player"
LAKE_CACHE_DIR=$(bash "$fir_root/scripts/fir-lake-cache-path.sh")
export LAKE_CACHE_DIR
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
illuminate_root=${ILLUMINATE_ROOT:-$(realpath .illuminate)}

node --test export-selection-package.test.mjs build-check.test.mjs
node check-native-capture.mjs
lake --keep-toolchain --reconfigure -KilluminateRoot="$illuminate_root" \
  build IlluminateFirNative.Examples IlluminateFirNative.SelectionExamples
node smoke.mjs
node selection-smoke.mjs
ILLUMINATE_ROOT="$illuminate_root" node check-player-traces.mjs
bash "$here/build.sh"

test "$package" = "$(realpath _build/illuminate-player-current)"
test "$selection_package" = \
  "$(realpath _build/illuminate-selection-player-current)"
(
  cd "$package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)
(
  cd "$selection_package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)
