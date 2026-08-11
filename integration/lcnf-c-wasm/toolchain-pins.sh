#!/usr/bin/env bash
# shellcheck disable=SC2034

FIR_LCNF_C_LEAN_VERSION="4.33.0"
FIR_LCNF_C_LEAN_COMMIT="d8b18978322de05a8f3dba51ef03cf5461676c17"

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
