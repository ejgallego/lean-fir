#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
fir_root=$(cd "$here/../.." && pwd)
if ! cmp -s "$here/lean-toolchain" "$fir_root/lean-toolchain"; then
  echo "Illuminate player recipe must use FIR's current Lean toolchain" >&2
  exit 1
fi
if [[ -n "${LEAN_TOOLCHAIN:-}" && "$LEAN_TOOLCHAIN" != "$(<"$fir_root/lean-toolchain")" ]]; then
  echo "LEAN_TOOLCHAIN must not override the current FIR pin" >&2
  exit 1
fi
for path in _build _build/illuminate-player-packages \
  _build/illuminate-selection-player-packages \
  _build/illuminate-player-current _build/illuminate-selection-player-current; do
  if [[ -e "$here/$path" || -L "$here/$path" ]]; then
    resolved=$(realpath -m "$here/$path")
    case "$resolved" in
      "$here/_build"|"$here/_build/"*) ;;
      *) echo "recipe output escapes its local _build: $path -> $resolved" >&2; exit 1 ;;
    esac
  fi
done
export TMPDIR="$fir_root/.deps/tmp/illuminate-player"
mkdir -p "$TMPDIR"
LAKE_CACHE_DIR=$(bash "$fir_root/scripts/fir-lake-cache-path.sh")
export LAKE_CACHE_DIR
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
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
if ! test -x "$fir_root/.deps/lcnf-c-wasm/emsdk/upstream/bin/wasm-opt"; then
  echo "missing recipe Binaryen; run integration/lcnf-c-wasm/setup-emscripten.sh from FIR root" >&2
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
