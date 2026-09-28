#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"

usage() {
  cat <<'EOF'
usage: setup-emscripten.sh [--runtime-profile threaded|unthreaded]

Build the pinned Lean runtime, Init, and Std archives for Emscripten.
The selected compiler determines the exact Lean source and archive directory.
EOF
}

die() {
  echo "setup-emscripten.sh: $*" >&2
  exit 1
}

runtime_profile="threaded"
while (($# > 0)); do
  case "$1" in
    --runtime-profile)
      if (($# < 2)); then
        die "$1 requires a value"
      fi
      runtime_profile="$2"
      shift 2
      ;;
    --help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

case "$runtime_profile" in
  threaded) multi_thread="ON" ;;
  unthreaded) multi_thread="OFF" ;;
  *)
    die "unsupported runtime profile: $runtime_profile"
    ;;
esac

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"
fir_lcnf_c_select_lean "$repo_root" || die "selected Lean compiler is unsupported"
fir_lcnf_c_runtime_paths "$deps_root" "$runtime_profile"
lean_build="$FIR_LCNF_C_LEAN_BUILD"

emsdk_dir="$deps_root/emsdk"
lean_src="$FIR_LCNF_C_LEAN_SOURCE"
# The two UV stubs still have the older ABI in both accepted source commits.
# The exact patch is checked against the selected checkout before any build.
lean_patch="$lane_dir/patches/lean-4.33.0-emscripten-uv-stubs.patch"
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
  die "Lean Emscripten compatibility patch does not match the selected source"
fi
modified_source="$(git -C "$lean_src" diff --name-only HEAD)"
expected_modified_source=$'stage0/src/runtime/uv/event_loop.cpp\nstage0/src/runtime/uv/system.cpp'
if [[ "$modified_source" != "$expected_modified_source" ]]; then
  die "Lean source has changes outside the reviewed Emscripten UV patch"
fi

export EMSDK_QUIET=1
# shellcheck disable=SC1091
source "$emsdk_dir/emsdk_env.sh"

emcmake cmake \
  -S "$lean_src/stage0/src" \
  -B "$lean_build" \
  -DCMAKE_BUILD_TYPE=Release \
  -DSTAGE=0 \
  "-DMULTI_THREAD=$multi_thread" \
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

stdlib_cflags="-O3 -DNDEBUG -flto -fomit-frame-pointer -ffunction-sections -fdata-sections -fno-fast-math -ffp-contract=off"

build_stdlib_archive() {
  local package="$1"
  (
    cd "$lean_src/stage0/src"
    "$lean_build/bin/leanmake" \
      --no-print-directory \
      --jobs "$jobs" \
      lib lib.export \
      "PKG=$package" \
      C_ONLY=1 \
      "C_OUT=$lean_src/stage0/stdlib" \
      "OUT=$lean_build/lib" \
      "LIB_OUT=$lean_build/lib/lean" \
      "OLEAN_OUT=$lean_build/lib/lean" \
      "TEMP_OUT=$lean_build/lib/temp" \
      "LEANC=$lean_build/leanc.sh" \
      "LEAN_AR=$emsdk_dir/upstream/emscripten/emar" \
      "LEANC_OPTS=$stdlib_cflags"
  )
}

build_stdlib_archive Init
build_stdlib_archive Std

for archive in libleanrt.a libInit.a libStd.a; do
  test -f "$lean_build/lib/lean/$archive"
done
test -f "$lean_build/libuv/src/libuv/libuv.a"
test -f "$lean_build/include/lean/lean.h"
receipt="$lean_build/fir-runtime-identity.txt"
fir_lcnf_c_runtime_receipt "$lean_src" "$lean_build" "$runtime_profile" > "$receipt.tmp"
mv -f "$receipt.tmp" "$receipt"

printf 'Emscripten %s and Lean runtime/Init/Std %s (%s) are ready in %s\n' \
  "$FIR_LCNF_C_EMSDK_VERSION" \
  "$FIR_LCNF_C_LEAN_VERSION" \
  "$runtime_profile" \
  "$lean_build"
