#!/usr/bin/env bash
# Build Ubuntu's maintained 0.9.0 source: Jammy's 0.6.1 lacks --disable-userns.
# Both hashes are from bubblewrap_0.9.0-1ubuntu0.3.dsc in Ubuntu's archive.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch="$root/.deps/ci-bwrap"
mkdir -p "$scratch/tmp" "$scratch/bin"
export TMPDIR="$scratch/tmp"
source_dir="$(mktemp -d "$scratch/source.XXXXXX")"
base=https://archive.ubuntu.com/ubuntu/pool/main/b/bubblewrap
curl -fsSL --retry 3 "$base/bubblewrap_0.9.0.orig.tar.xz" -o "$scratch/source.tar.xz"
curl -fsSL --retry 3 "$base/bubblewrap_0.9.0-1ubuntu0.3.debian.tar.xz" -o "$scratch/ubuntu.tar.xz"
printf '%s  %s\n' \
  c6347eaced49ac0141996f46bba3b089e5e6ea4408bc1c43bab9f2d05dd094e1 "$scratch/source.tar.xz" \
  4d6c71db380bb69d19a09501bd5caec92e46bf54c7f505805e75687daf783939 "$scratch/ubuntu.tar.xz" \
  | sha256sum --check --status
tar -xJf "$scratch/source.tar.xz" --strip-components=1 -C "$source_dir"
tar -xJf "$scratch/ubuntu.tar.xz" -C "$source_dir"
(
  cd "$source_dir"
  while IFS= read -r patch_name; do
    [[ -z "$patch_name" || "$patch_name" == \#* ]] && continue
    patch -p1 < "debian/patches/$patch_name"
  done < debian/patches/series
  meson setup build -Dtests=false -Dman=disabled \
    -Dbash_completion=disabled -Dzsh_completion=disabled
  meson compile -C build -j2
)
install -m755 "$source_dir/build/bwrap" "$scratch/bin/bwrap"
"$scratch/bin/bwrap" --version
"$scratch/bin/bwrap" --die-with-parent --new-session --unshare-all --unshare-user \
  --disable-userns --assert-userns-disabled --cap-drop ALL \
  --ro-bind / / --proc /proc --dev /dev -- true
if [[ -n "${GITHUB_PATH:-}" ]]; then
  printf '%s\n' "$scratch/bin" >> "$GITHUB_PATH"
fi
