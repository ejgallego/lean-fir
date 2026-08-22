#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"

git -C "$repo_root" diff --check
node --check "$lane_dir/enhance-manifest.mjs"
node --check "$lane_dir/benchmark.mjs"
node --check "$lane_dir/illuminate-selection-player-emscripten-adapter.mjs"
node --check "$lane_dir/smoke.mjs"
cc -std=c11 -Wall -Wextra -Werror -fsyntax-only \
  -I "$(lake -d "$repo_root" env lean --print-prefix)/include" \
  "$lane_dir/runtime/selection-player-bridge.c"

export LAKE_CACHE_DIR="$(bash "$repo_root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true

# Materialize and validate the exact pinned source view before the native wire
# check.  A developer worktree may already have `.illuminate`, but relying on
# that ignored convenience state makes a clean checkout fail before packaging.
"$lane_dir/package.sh"

native_illuminate_root="$repo_root/.deps/illuminate-player-llvm/source-view"
lake -d "$lane_dir" --reconfigure \
  "-KilluminateRoot=$native_illuminate_root" \
  build wireTests
"$lane_dir/.lake/build/bin/wireTests"
