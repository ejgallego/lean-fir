#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

emsdk_dir="$deps_root/emsdk"
lean_src="$deps_root/lean4"
lean_build="$deps_root/lean4-emscripten-build"
lean_patch="$lane_dir/patches/lean-4.32.0-emscripten-uv-stubs.patch"
jobs="${FIR_WASM_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf '4')}"

for tool in git cmake make; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required setup tool not found: $tool" >&2
    exit 1
  fi
done

mkdir -p "$deps_root"

if [[ ! -d "$emsdk_dir/.git" ]]; then
  git clone \
    --depth 1 \
    --branch "$FIR_LCNF_C_EMSDK_VERSION" \
    https://github.com/emscripten-core/emsdk.git \
    "$emsdk_dir"
fi

emsdk_commit="$(git -C "$emsdk_dir" rev-parse HEAD)"
if [[ "$emsdk_commit" != "$FIR_LCNF_C_EMSDK_COMMIT" ]]; then
  echo "emsdk checkout mismatch: expected $FIR_LCNF_C_EMSDK_COMMIT, got $emsdk_commit" >&2
  exit 1
fi

"$emsdk_dir/emsdk" install "$FIR_LCNF_C_EMSDK_VERSION"
"$emsdk_dir/emsdk" activate "$FIR_LCNF_C_EMSDK_VERSION"

if [[ ! -d "$lean_src/.git" ]]; then
  git init "$lean_src"
  git -C "$lean_src" remote add origin https://github.com/leanprover/lean4.git
  git -C "$lean_src" fetch --depth 1 origin "$FIR_LCNF_C_LEAN_COMMIT"
  git -C "$lean_src" checkout --detach FETCH_HEAD
fi

lean_commit="$(git -C "$lean_src" rev-parse HEAD)"
if [[ "$lean_commit" != "$FIR_LCNF_C_LEAN_COMMIT" ]]; then
  echo "Lean source mismatch: expected $FIR_LCNF_C_LEAN_COMMIT, got $lean_commit" >&2
  exit 1
fi

if git -C "$lean_src" apply --reverse --check "$lean_patch" >/dev/null 2>&1; then
  :
elif git -C "$lean_src" apply --check "$lean_patch"; then
  git -C "$lean_src" apply "$lean_patch"
else
  echo "Lean Emscripten compatibility patch does not match the pinned source" >&2
  exit 1
fi

export EMSDK_QUIET=1
# shellcheck disable=SC1091
source "$emsdk_dir/emsdk_env.sh"

emcmake cmake \
  -S "$lean_src/stage0/src" \
  -B "$lean_build" \
  -DCMAKE_BUILD_TYPE=Release \
  -DSTAGE=0 \
  -DMULTI_THREAD=ON \
  -DUSE_GMP=OFF \
  -DUSE_MIMALLOC=OFF \
  -DMMAP=OFF \
  -DUSE_LAKE=OFF \
  -DCCACHE=OFF \
  -DLLVM=OFF \
  -DLEAN_STANDALONE=ON \
  -DINSTALL_CADICAL=OFF \
  -DINSTALL_LEANTAR=OFF

cmake --build "$lean_build" --target leanrt --parallel "$jobs"

test -f "$lean_build/lib/lean/libleanrt.a"
printf 'Emscripten %s and Lean runtime %s are ready in %s\n' \
  "$FIR_LCNF_C_EMSDK_VERSION" \
  "$FIR_LCNF_C_LEAN_VERSION" \
  "$deps_root"
