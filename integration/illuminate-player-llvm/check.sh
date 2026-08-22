#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"

git -C "$repo_root" diff --check
node --check "$lane_dir/enhance-manifest.mjs"
node --check "$lane_dir/illuminate-selection-player-emscripten-adapter.mjs"
node --check "$lane_dir/smoke.mjs"
cc -std=c11 -Wall -Wextra -Werror -fsyntax-only \
  -I "$(lake -d "$repo_root" env lean --print-prefix)/include" \
  "$lane_dir/runtime/selection-player-bridge.c"

export LAKE_CACHE_DIR="$(bash "$repo_root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true
lake -d "$lane_dir" build wireTests
"$lane_dir/.lake/build/bin/wireTests"

"$lane_dir/package.sh"
