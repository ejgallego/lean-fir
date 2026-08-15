#!/usr/bin/env bash
set -euo pipefail

directory="$(cd "$(dirname "$0")" && pwd)"
cd "$directory"

: "${LEAN_ZIP_ROOT:=/tmp/fir-lean-zip-273d}"
: "${ZIP_COMMON_ROOT:=/tmp/fir-zip-common-4425}"
export LEAN_ZIP_ROOT ZIP_COMMON_ROOT

node --test export-raw-package.test.mjs
FIR_ALLOW_DIRTY_PACKAGE="${FIR_ALLOW_DIRTY_PACKAGE:-1}" node package.mjs

if [[ -n "${FIR_BROWSER:-}" ]]; then
  ./browser-check.sh "$FIR_BROWSER"
fi
