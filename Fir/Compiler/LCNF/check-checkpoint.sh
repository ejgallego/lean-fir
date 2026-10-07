#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
cd "$root"
export TMPDIR="$root/.deps/tmp/checkpoint"
mkdir -p "$TMPDIR"
LAKE_CACHE_DIR=$(bash "$root/scripts/fir-lake-cache-path.sh")
export LAKE_CACHE_DIR LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true

lake build Fir.Compiler.LCNF.CheckpointExamples \
  Fir.Compiler.LCNF.CheckpointShadowExamples Fir.Compiler.LCNF.CheckpointReadback
runner=$(mktemp -d "$TMPDIR/readback.XXXXXX")
trap 'rm -rf -- "$runner"' EXIT
cp "$here/CheckpointMain.lean.in" "$runner/Main.lean"
lake env lean --run "$runner/Main.lean"
lake --keep-toolchain -d integration/lean-zip build +LeanZipFir.CaptureCacheExamples:olean
