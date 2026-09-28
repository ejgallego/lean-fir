#!/usr/bin/env bash
# shellcheck disable=SC2034

# The selected Lean compiler, not this file, determines the runtime source.
# Keep the accepted transition identities explicit so an unrelated toolchain
# cannot silently enter the C/Wasm path.
fir_lcnf_c_parse_lean_identity() {
  local version="$1"
  if [[ ! "$version" =~ ^Lean\ \(version\ ([0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?),.*commit\ ([0-9a-f]{40}), ]]; then
    echo "unrecognized Lean compiler identity: $version" >&2
    return 1
  fi
  FIR_LCNF_C_LEAN_VERSION="${BASH_REMATCH[1]}"
  FIR_LCNF_C_LEAN_COMMIT="${BASH_REMATCH[3]}"
  case "$FIR_LCNF_C_LEAN_VERSION:$FIR_LCNF_C_LEAN_COMMIT" in
    4.33.0:d8b18978322de05a8f3dba51ef03cf5461676c17|\
    4.34.0-rc2:6a10ac8c22beadecabdbb0919c2b50214762f91d|\
    4.34.1:5045d0056413266e57c625dcd7c365b10e377c52) ;;
    *)
      echo "unsupported Lean compiler identity: $version" >&2
      return 1
      ;;
  esac
}

fir_lcnf_c_select_lean() {
  local repo_root="$1" version
  version="$(lake -d "$repo_root" env lean --version)" || return 1
  fir_lcnf_c_parse_lean_identity "$version"
}

fir_lcnf_c_runtime_paths() {
  local deps_root="$1" profile="$2"
  FIR_LCNF_C_LEAN_SOURCE="$deps_root/lean4-$FIR_LCNF_C_LEAN_COMMIT"
  FIR_LCNF_C_LEAN_BUILD="$deps_root/lean4-emscripten-build-$FIR_LCNF_C_LEAN_COMMIT-$profile"
}

fir_lcnf_c_runtime_receipt() {
  local source="$1" build="$2" profile="$3" archive
  printf 'lean-version %s\nlean-commit %s\nprofile %s\n' \
    "$FIR_LCNF_C_LEAN_VERSION" "$FIR_LCNF_C_LEAN_COMMIT" "$profile"
  printf 'source-commit %s\n' "$(git -C "$source" rev-parse HEAD)"
  printf 'source-diff %s\n' "$(git -C "$source" diff --binary HEAD | sha256sum | cut -d' ' -f1)"
  for archive in libleanrt.a libInit.a libStd.a; do
    printf '%s %s\n' "$archive" "$(sha256sum "$build/lib/lean/$archive" | cut -d' ' -f1)"
  done
  printf 'libuv.a %s\n' "$(sha256sum "$build/libuv/src/libuv/libuv.a" | cut -d' ' -f1)"
  printf 'lean.h %s\n' "$(sha256sum "$build/include/lean/lean.h" | cut -d' ' -f1)"
}

fir_lcnf_c_verify_runtime_receipt() {
  local source="$1" build="$2" profile="$3"
  [[ -f "$build/fir-runtime-identity.txt" ]] &&
    cmp -s "$build/fir-runtime-identity.txt" \
      <(fir_lcnf_c_runtime_receipt "$source" "$build" "$profile")
}

FIR_LCNF_C_EMSDK_VERSION="5.0.3"
FIR_LCNF_C_EMSDK_COMMIT="a620cf1d71c62dfdfbb0c01fe0a371e2af2dda6c"

FIR_LCNF_C_WASI_SDK_RELEASE="33"
FIR_LCNF_C_WASI_SDK_VERSION="33.0"

fir_lcnf_c_wasi_sdk_asset() {
  local host_os host_arch
  host_os="$(uname -s)"
  host_arch="$(uname -m)"

  case "$host_os:$host_arch" in
    Linux:x86_64)
      printf '%s %s\n' \
        "wasi-sdk-33.0-x86_64-linux.tar.gz" \
        "0ba8b5bfaeb2adf3f29bab5841d76cf5318ab8e1642ea195f88baba1abd47bce"
      ;;
    Linux:aarch64|Linux:arm64)
      printf '%s %s\n' \
        "wasi-sdk-33.0-arm64-linux.tar.gz" \
        "4f98ee738c7abb45c81a94d1461fc53cc569d1cd01498951c8184d841a027844"
      ;;
    Darwin:x86_64)
      printf '%s %s\n' \
        "wasi-sdk-33.0-x86_64-macos.tar.gz" \
        "18f3f201ba9734e6a4455b0b6410690395a55e9ffa9f6f5066f66083a94b93b3"
      ;;
    Darwin:arm64)
      printf '%s %s\n' \
        "wasi-sdk-33.0-arm64-macos.tar.gz" \
        "85c997a2665ead91673b5bb88b7d0df3fc8900df3bfa244f720d478187bbdc78"
      ;;
    *)
      echo "unsupported wasi-sdk host: $host_os $host_arch" >&2
      return 1
      ;;
  esac
}
