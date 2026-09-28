#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

accepted_433='Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)'
accepted_rc2='Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)'
accepted_4341='Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
fir_lcnf_c_parse_lean_identity "$accepted_433"
[[ "$FIR_LCNF_C_LEAN_VERSION" == 4.33.0 ]]
fir_lcnf_c_parse_lean_identity "$accepted_rc2"
[[ "$FIR_LCNF_C_LEAN_VERSION" == 4.34.0-rc2 ]]
fir_lcnf_c_parse_lean_identity "$accepted_4341"
[[ "$FIR_LCNF_C_LEAN_COMMIT" == 5045d0056413266e57c625dcd7c365b10e377c52 ]]
if fir_lcnf_c_parse_lean_identity "${accepted_4341/5045d0056413266e57c625dcd7c365b10e377c52/d8b18978322de05a8f3dba51ef03cf5461676c17}" 2>/dev/null; then
  echo 'accepted a wrong version/commit pair' >&2
  exit 1
fi
if fir_lcnf_c_parse_lean_identity 'Lean (version 4.35.0, commit unknown)' 2>/dev/null; then
  echo 'accepted an unknown compiler identity' >&2
  exit 1
fi

fir_lcnf_c_select_lean "$repo_root"
mkdir -p "$repo_root/.deps"
scratch="$(mktemp -d "$repo_root/.deps/lcnf-c-identity.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
fake_deps="$scratch/deps"
fir_lcnf_c_runtime_paths "$fake_deps" threaded
source_dir="$FIR_LCNF_C_LEAN_SOURCE"
build_dir="$FIR_LCNF_C_LEAN_BUILD"
mkdir -p "$source_dir" "$build_dir/lib/lean" "$build_dir/libuv/src/libuv" "$build_dir/include/lean" "$fake_deps/emsdk"
: > "$fake_deps/emsdk/emsdk_env.sh"
git -C "$source_dir" init -q
printf 'source\n' > "$source_dir/probe"
git -C "$source_dir" add probe
git -C "$source_dir" -c user.name=FIR -c user.email=fir@example.invalid commit -qm source
for archive in libleanrt.a libInit.a libStd.a; do
  printf '%s\n' "$archive" > "$build_dir/lib/lean/$archive"
done
printf 'libuv\n' > "$build_dir/libuv/src/libuv/libuv.a"
printf 'header\n' > "$build_dir/include/lean/lean.h"
fir_lcnf_c_runtime_receipt "$source_dir" "$build_dir" threaded > "$build_dir/fir-runtime-identity.txt"
fir_lcnf_c_verify_runtime_receipt "$source_dir" "$build_dir" threaded
if fir_lcnf_c_verify_runtime_receipt "$source_dir" "$build_dir" unthreaded; then
  echo 'accepted wrong runtime profile' >&2
  exit 1
fi
printf 'changed\n' >> "$build_dir/lib/lean/libStd.a"
if fir_lcnf_c_verify_runtime_receipt "$source_dir" "$build_dir" threaded; then
  echo 'accepted altered runtime archive' >&2
  exit 1
fi
fir_lcnf_c_runtime_receipt "$source_dir" "$build_dir" threaded > "$build_dir/fir-runtime-identity.txt"
printf 'changed\n' >> "$source_dir/probe"
if fir_lcnf_c_verify_runtime_receipt "$source_dir" "$build_dir" threaded; then
  echo 'accepted altered runtime source' >&2
  exit 1
fi
if FIR_LCNF_C_WASM_DEPS="$fake_deps" bash "$lane_dir/build-emscripten.sh" "$lane_dir/Smoke.lean" > "$scratch/build-negative.log" 2>&1; then
  echo 'accepted runtime source from another Lean commit' >&2
  exit 1
fi
if ! grep -q 'Lean source does not match selected compiler commit' "$scratch/build-negative.log"; then
  echo 'source-commit mismatch did not fail before linking' >&2
  exit 1
fi
printf 'generic C compiler/source/archive identity: OK\n'
