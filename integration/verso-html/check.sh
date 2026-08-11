#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
verso_root=${VERSO_ROOT:-$(realpath .verso)}

lake --keep-toolchain --reconfigure -KversoRoot="$verso_root" \
  build VersoFirHtml.Compile
VERSO_ROOT="$verso_root" node package.mjs
package=$(realpath _build/verso-html-current)
VERSO_ROOT="$verso_root" node package.mjs
test "$package" = "$(realpath _build/verso-html-current)"

(
  cd "$package"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)
VERSO_ROOT="$verso_root" node check-html.mjs "$package"

validator="$verso_root/demos/vir-pretty/scripts/validate-native-html-package.py"
if test -f "$validator"; then
  python3 "$validator" "$package"
fi
if test -n "${FIR_BROWSER:-}"; then
  bash browser-check.sh "$FIR_BROWSER"
fi

echo "Verso HTML package: $package"
