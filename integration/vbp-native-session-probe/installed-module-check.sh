#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
fir=$(cd "$here/../.." && pwd)
export LAKE_CACHE_DIR="$(bash "$fir/scripts/fir-lake-cache-path.sh")" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$fir/.deps/native-session-probe/tmp"
mkdir -p "$TMPDIR" "$LAKE_CACHE_DIR"
chmod 700 "$LAKE_CACHE_DIR"
# Refresh the actual renderer frontier first; never promote a stale inventory.
bash "$here/module-assembly-check.sh"
cd "$here"
lake --keep-toolchain -KpostponeCompile=false env lean InstalledModuleCapture.lean
node installed-module-check.mjs
