#!/usr/bin/env bash
# Ubuntu 22.04 ships strace 5.16, which lacks the recorder's --kill-on-exit.
# Keep the runner OS and recorder guarantees; build the authenticated 6.8 source.
# SHA-256: https://archive.ubuntu.com/ubuntu/pool/main/s/strace/strace_6.8-0ubuntu2.dsc
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch="$root/.deps/ci-strace"
mkdir -p "$scratch/tmp"
export TMPDIR="$scratch/tmp"
archive="$scratch/strace-6.8.tar.xz"
curl -fsSL --retry 3 \
  https://archive.ubuntu.com/ubuntu/pool/main/s/strace/strace_6.8.orig.tar.xz \
  -o "$archive"
printf '%s  %s\n' \
  ba6950a96824cdf93a584fa04f0a733896d2a6bc5f0ad9ffe505d9b41e970149 \
  "$archive" | sha256sum --check --status
mkdir -p "$scratch/source" "$scratch/bin"
tar -xJf "$archive" --strip-components=1 -C "$scratch/source"
(
  cd "$scratch/source"
  ./configure --enable-mpers=no --without-libunwind
  make -j2
)
install -m755 "$scratch/source/src/strace" "$scratch/bin/strace"
"$scratch/bin/strace" --version
"$scratch/bin/strace" --kill-on-exit -qq -o "$scratch/preflight.strace" -- true
if [[ -n "${GITHUB_PATH:-}" ]]; then
  printf '%s\n' "$scratch/bin" >> "$GITHUB_PATH"
fi
