#!/usr/bin/env bash
set -euo pipefail

directory="$(cd "$(dirname "$0")" && pwd)"
cd "$directory"

fir_root="$(cd "$directory/../.." && pwd)"
: "${LEAN_ZIP_ROOT:=$fir_root/.deps/source-views/lean-zip}"
: "${ZIP_COMMON_ROOT:=$fir_root/.deps/source-views/zip-common}"
export LEAN_ZIP_ROOT ZIP_COMMON_ROOT

node --test export-raw-package.test.mjs
FIR_ALLOW_DIRTY_PACKAGE="${FIR_ALLOW_DIRTY_PACKAGE:-1}" node package.mjs

if [[ -n "${FIR_BROWSER:-}" ]]; then
  ./browser-check.sh "$FIR_BROWSER"
fi
