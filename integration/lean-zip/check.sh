#!/usr/bin/env bash
set -euo pipefail

directory="$(cd "$(dirname "$0")" && pwd)"
cd "$directory"

: "${LEAN_ZIP_ROOT:=/tmp/fir-lean-zip-30737}"
: "${ZIP_COMMON_ROOT:=/tmp/fir-zip-common-4425}"
export LEAN_ZIP_ROOT ZIP_COMMON_ROOT

FIR_ALLOW_DIRTY_PACKAGE="${FIR_ALLOW_DIRTY_PACKAGE:-1}" node package.mjs

if [[ -n "${FIR_BROWSER:-}" ]]; then
  ./browser-check.sh "$FIR_BROWSER"
fi
