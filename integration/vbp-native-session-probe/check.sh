#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
fir=$(cd "$here/../.." && pwd)
cd "$here"
export LAKE_CACHE_DIR="$(bash "$fir/scripts/fir-lake-cache-path.sh")" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
# This fixture has an exact different toolchain; never use the 4.33 cache scope.
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$fir/.deps/native-session-probe/tmp"
mkdir -p "$TMPDIR" "$LAKE_CACHE_DIR"
chmod 700 "$LAKE_CACHE_DIR"
node prepare.mjs
lake --keep-toolchain build Probe
lake --keep-toolchain env lean -DmaxHeartbeats=0 Emit.lean
node validate.mjs
