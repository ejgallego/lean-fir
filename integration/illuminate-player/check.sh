#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
illuminate_root=${ILLUMINATE_ROOT:-$(realpath .illuminate)}

lake --keep-toolchain -KilluminateRoot="$illuminate_root" \
  build IlluminateFirNative.Examples
ILLUMINATE_ROOT="$illuminate_root" node package.mjs
package=$(realpath _build/illuminate-player-current)
node smoke.mjs
ILLUMINATE_ROOT="$illuminate_root" node check-player-traces.mjs
ILLUMINATE_ROOT="$illuminate_root" node package.mjs

test "$package" = "$(realpath _build/illuminate-player-current)"
(
  cd "$package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)
