#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
fir=$(cd "$here/../.." && pwd)
state="$fir/.deps/native-session-probe"
export LAKE_CACHE_DIR="$(bash "$fir/scripts/fir-lake-cache-path.sh")" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$state/tmp"
mkdir -p "$TMPDIR" "$LAKE_CACHE_DIR"
chmod 700 "$LAKE_CACHE_DIR"
cd "$here"
node prepare.mjs
# Lake supplies the real resolved setups and builds imports from pinned source.
lake --keep-toolchain -KpostponeCompile=false build Fir.Wasm.Emit.ModuleSource +VersoBlueprintVir.Preview.Renderer
lake --keep-toolchain -KpostponeCompile=false env lean ModuleCapture.lean
capture() {
  lake --keep-toolchain -KpostponeCompile=false env lean --run ModuleCapture.lean "$@"
}
for round in first repeat; do
  capture "$state/sources/verso/src/verso/Verso/Doc.lean" \
    "$state/sources/verso/.lake/build/ir/Verso/Doc.setup.json" \
    "$state/ordinary-module/$round/verso-doc" \
    _private.Verso.Doc.0.Verso.Doc.DescItem.toJson
  capture "$state/sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean" \
    "$here/.lake/build/ir/VersoBlueprintVir/Preview/Renderer.setup.json" \
    "$state/ordinary-module/$round/renderer" \
    VersoBlueprint.Experimental.VirPreview.Renderer.render
done
node module-capture-check.mjs "$state/ordinary-module"
