#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
verso_root=${VERSO_ROOT:-$(realpath .verso)}

lake --keep-toolchain --reconfigure -KversoRoot="$verso_root" \
  build VersoFirFlat.Examples
VERSO_ROOT="$verso_root" node package.mjs
package=$(realpath _build/verso-flat-current)
VERSO_ROOT="$verso_root" node package.mjs
test "$package" = "$(realpath _build/verso-flat-current)"
if test "${VERSO_ALLOW_UNPUBLISHED_SOURCE:-0}" != 1; then
  node -e '
    const fs = require("node:fs");
    const build = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
    if (build.provisional) {
      throw new Error(build.provisionalReason ?? "package source is provisional");
    }
  ' "$package/BUILD.json"
fi

(
  cd "$package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)
VERSO_ROOT="$verso_root" node check-flat.mjs "$package"

validator="$verso_root/demos/vir-pretty/scripts/validate-native-flat-package.py"
if test -f "$validator"; then
  python3 "$validator" "$package"
fi
if test -n "${FIR_BROWSER:-}"; then
  bash browser-check.sh "$FIR_BROWSER"
fi

echo "Verso Flat package: $package"
