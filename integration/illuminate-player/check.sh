#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
illuminate_root=${ILLUMINATE_ROOT:-$(realpath .illuminate)}
illuminate_revision=$(node -e '
  const fs = require("node:fs");
  const contract = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
  process.stdout.write(contract.revision);
' "$here/illuminate-source.json")
actual_illuminate_revision=$(git -C "$illuminate_root" rev-parse HEAD)
if test "$actual_illuminate_revision" != "$illuminate_revision"; then
  echo "Illuminate revision mismatch: expected $illuminate_revision, found $actual_illuminate_revision" >&2
  exit 1
fi
if test -n "$(git -C "$illuminate_root" status --porcelain)"; then
  echo "Illuminate checkout must be clean: $illuminate_root" >&2
  exit 1
fi

node --test export-selection-package.test.mjs
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
