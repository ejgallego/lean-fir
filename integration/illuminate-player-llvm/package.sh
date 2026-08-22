#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
builder="$repo_root/integration/lcnf-c-wasm/build-emscripten.sh"
source_contract="$lane_dir/illuminate-source.json"
illuminate_repo="${ILLUMINATE_ROOT:-/home/egallego/lean/illuminate}"
build_root="${FIR_ILLUMINATE_LLVM_BUILD_ROOT:-$lane_dir/_build}"
source_root="$repo_root/.deps/illuminate-player-llvm/source-view"
stage_root="$build_root/staging"
build_dir="$stage_root/package"

revision="$(node -e 'const c=require(process.argv[1]); process.stdout.write(c.revision)' "$source_contract")"
actual_revision="$(git -C "$illuminate_repo" rev-parse "$revision^{commit}")"
if [[ "$actual_revision" != "$revision" ]]; then
  echo "Illuminate revision mismatch: expected $revision, got $actual_revision" >&2
  exit 1
fi

rm -rf "$source_root" "$stage_root"
mkdir -p "$source_root" "$build_dir" "$source_root/runtime"
git -C "$illuminate_repo" archive "$revision" \
  src/Illuminate/Animation/Types.lean \
  src/Illuminate/Animation/Player.lean \
  src/Illuminate/Animation/FirLive.lean \
  src/Illuminate/Animation/FirSelection.lean |
  tar -x -C "$source_root" --strip-components=1
install -m 0644 "$lane_dir/IlluminateLlvmSelection.lean" \
  "$source_root/IlluminateLlvmSelection.lean"
install -m 0644 "$lane_dir/runtime/selection-player-bridge.c" \
  "$source_root/runtime/selection-player-bridge.c"

node - "$source_contract" "$source_root" <<'NODE'
const { createHash } = require("node:crypto");
const { readFileSync } = require("node:fs");
const path = require("node:path");
const contract = require(process.argv[2]);
for (const source of contract.relevantFiles) {
  const local = path.join(process.argv[3], source.path.replace(/^src\//, ""));
  const digest = createHash("sha256").update(readFileSync(local)).digest("hex");
  if (digest !== source.sha256) {
    throw new Error(`${source.path}: expected ${source.sha256}, got ${digest}`);
  }
}
NODE

"$builder" \
  --runtime-profile unthreaded \
  --root "$source_root" \
  --out-dir "$build_dir" \
  --name illuminate-selection-player \
  --extra-source "$source_root/Illuminate/Animation/Types.lean" \
  --extra-source "$source_root/Illuminate/Animation/Player.lean" \
  --extra-source "$source_root/Illuminate/Animation/FirSelection.lean" \
  --extra-c-source "$source_root/runtime/selection-player-bridge.c" \
  --heap-view \
  --export fir_illuminate_selection_input_alloc \
  --export fir_illuminate_selection_create \
  --export fir_illuminate_selection_created_handle \
  --export fir_illuminate_selection_dispatch \
  --export fir_illuminate_selection_dispatch_tick_scalar \
  --export fir_illuminate_selection_result_ptr \
  --export fir_illuminate_selection_result_len \
  --export fir_illuminate_selection_dispose \
  --export fir_illuminate_selection_live_count \
  --export fir_illuminate_selection_release \
  "$source_root/IlluminateLlvmSelection.lean"

install -m 0644 "$repo_root/integration/lcnf-c-wasm/emscripten-loader.mjs" \
  "$build_dir/emscripten-loader.mjs"
install -m 0644 "$lane_dir/illuminate-selection-player-emscripten-adapter.mjs" \
  "$build_dir/illuminate-selection-player-emscripten-adapter.mjs"
install -m 0644 "$lane_dir/README.md" "$build_dir/README.md"
install -m 0644 "$lane_dir/smoke.mjs" "$build_dir/smoke.mjs"

fir_commit="$(git -C "$repo_root" rev-parse HEAD)"
fir_dirty=false
if [[ -n "$(git -C "$repo_root" status --short --untracked-files=all)" ]]; then
  fir_dirty=true
fi
node "$lane_dir/enhance-manifest.mjs" \
  "$build_dir/illuminate-selection-player.manifest.json" \
  "$source_contract" \
  "$fir_commit" \
  "$fir_dirty"

(
  cd "$build_dir"
  LC_ALL=C sha256sum \
    README.md \
    emscripten-loader.mjs \
    illuminate-selection-player-emscripten-adapter.mjs \
    illuminate-selection-player.manifest.json \
    illuminate-selection-player.mjs \
    illuminate-selection-player.wasm \
    smoke.mjs > SHA256SUMS
  sha256sum -c SHA256SUMS
  node smoke.mjs
)

package_digest="$(sha256sum "$build_dir/SHA256SUMS")"
package_digest="${package_digest%% *}"
package_dir="$build_root/packages/illuminate-selection-player-${package_digest}"
mkdir -p "$build_root/packages"
if [[ -e "$package_dir" ]]; then
  diff -qr "$build_dir" "$package_dir"
  rm -rf "$build_dir"
else
  mv "$build_dir" "$package_dir"
fi
printf '%s\n' "$package_dir" > "$build_root/illuminate-selection-player-current.txt"
printf 'prepared immutable LLVM Illuminate selection-player package: %s\n' "$package_dir"
