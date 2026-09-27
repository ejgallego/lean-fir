#!/usr/bin/env bash
set -euo pipefail

# Reproduce from source objects only; never import another worktree's oleans.
if [[ $# != 2 ]]; then
  echo "usage: bash integration/talos/retained-initializer/check.sh LEAN_ZIP_REPO ZIP_COMMON_REPO" >&2
  exit 2
fi
root="$(cd "$(dirname "$0")/../../.." && pwd)"
zip_repo="$(cd "$1" && pwd)"
common_repo="$(cd "$2" && pwd)"
zip_commit=273d0d6cd9cab77c7f3489b0b0b1f6e543315d21
common_commit=4425bab1f9522307d77e8d485bc536149ba31c36
git -C "$zip_repo" cat-file -e "$zip_commit^{commit}"
git -C "$common_repo" cat-file -e "$common_commit^{commit}"
cd "$root"
project="$root/.deps/retained-rc2"
mkdir -p "$project/lean-zip" "$project/zip-common" "$root/.deps/tmp"
export TMPDIR="$root/.deps/tmp"
export LAKE_CACHE_DIR="$(bash "$root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
git -C "$zip_repo" archive "$zip_commit" | tar -x -C "$project/lean-zip"
git -C "$common_repo" archive "$common_commit" | tar -x -C "$project/zip-common"
cp lean-toolchain "$project/lean-toolchain"
cp Fir/Compiler/LCNF/retained-example/RetainedRC2.lean.in "$project/RetainedRC2.lean"
cp Fir/Compiler/LCNF/retained-example/Readback.lean.in "$project/Readback.lean"
cp integration/talos/retained-initializer/lakefile.lean.in "$project/lakefile.lean"
cp integration/talos/retained-initializer/RetainedDeclarations.lean "$project/RetainedDeclarations.lean"
cp integration/talos/retained-initializer/RetainedInitializer.lean "$project/RetainedInitializer.lean"
make talos-setup
lake -d .deps/talos-434/project build FirTalos.ConcreteArrayExternal FirTalos.ConcretePublicationExecution
cd "$project"
lake build RetainedInitializer
lake env lean Readback.lean
# Force real batch elaboration of the consumer and its exact axiom inventory.
lake env lean RetainedInitializer.lean
