#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
illuminate_root=${ILLUMINATE_ROOT:-$(realpath .illuminate)}

lake --keep-toolchain --reconfigure -KilluminateRoot="$illuminate_root" \
  build IlluminateFirNative.Examples IlluminateFirNative.SelectionExamples
ILLUMINATE_ROOT="$illuminate_root" node package.mjs
package=$(realpath _build/illuminate-player-current)
ILLUMINATE_ROOT="$illuminate_root" node selection-package.mjs
selection_package=$(realpath _build/illuminate-selection-player-current)
node smoke.mjs
node selection-smoke.mjs
ILLUMINATE_ROOT="$illuminate_root" node check-player-traces.mjs
ILLUMINATE_ROOT="$illuminate_root" node package.mjs
ILLUMINATE_ROOT="$illuminate_root" node selection-package.mjs

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
