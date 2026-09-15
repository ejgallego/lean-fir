#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
fir=$(cd "$here/../.." && pwd)
export LAKE_CACHE_DIR="$(bash "$fir/scripts/fir-lake-cache-path.sh")" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$fir/.deps/native-session-probe/tmp"
mkdir -p "$TMPDIR" "$LAKE_CACHE_DIR"
chmod 700 "$LAKE_CACHE_DIR"
cd "$here"
node prepare.mjs
lake --keep-toolchain -KpostponeCompile=false build Fir.Wasm.Emit.ModuleSource Fir.Wasm.Emit.NativeSymbol Probe.InstalledInputs +VersoBlueprintVir.Preview.Renderer
lake --keep-toolchain -KpostponeCompile=false env lean ModuleProduct.lean
FIR_NATIVE_SYMBOL_TEST_OUTPUT="$TMPDIR/native-symbol-test.wasm" \
  lake --keep-toolchain -KpostponeCompile=false env lean NativeSymbolTests.lean
node native-symbol-test.mjs "$TMPDIR/native-symbol-test.wasm"
if [[ " $* " == *" --lower "* ]]; then
  lake --keep-toolchain -KpostponeCompile=false build Fir.Wasm.Emit.ResidentLinker
  lake --keep-toolchain -KpostponeCompile=false env lean ../talos/artifact/RuntimeFrontierTests.lean
  lake --keep-toolchain -KpostponeCompile=false env lean LowerModuleProduct.lean
fi
node module-product-check.mjs "$@"
