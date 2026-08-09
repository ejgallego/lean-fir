#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
fir_root="$(cd "$here/../.." && pwd)"

usage() {
  cat <<'EOF'
usage: export-v3-package.sh output-directory

Build and validate the pinned Illuminate v3 player package, then copy its six
regular package files into a fresh caller-owned output directory.

ILLUMINATE_ROOT must name a clean checkout at the revision pinned by
illuminate-source.json.
EOF
}

if [[ "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi
if (($# != 1)); then
  usage >&2
  exit 1
fi
if [[ -z "${ILLUMINATE_ROOT:-}" ]]; then
  echo "ILLUMINATE_ROOT must name the exact clean Illuminate checkout" >&2
  exit 1
fi

illuminate_root="$(realpath "$ILLUMINATE_ROOT")"
output_arg="${1%/}"
if [[ -z "$output_arg" ]]; then
  output_arg="/"
fi
output_parent="$(dirname "$output_arg")"
output_name="$(basename "$output_arg")"
if [[ "$output_name" == "." || "$output_name" == ".." || \
      "$output_name" == "/" ]]; then
  echo "output directory must have a non-special final component: $output_arg" >&2
  exit 1
fi
if [[ -n "$(git -C "$fir_root" status --porcelain)" ]]; then
  echo "FIR checkout must be clean: $fir_root" >&2
  exit 1
fi

mkdir -p "$output_parent"
output_parent="$(cd "$output_parent" && pwd)"
output="$output_parent/$output_name"
if [[ -e "$output" || -L "$output" ]]; then
  echo "output directory must be fresh: $output" >&2
  exit 1
fi

ILLUMINATE_ROOT="$illuminate_root" "$here/check.sh"

package="$(realpath "$here/_build/illuminate-player-current")"
files=(
  BUILD.json
  SHA256SUMS
  illuminate-player-browser-adapter.mjs
  illuminate-player.wasm
  illuminate-player.wasm.json
  smoke.mjs
)

stage="$(mktemp -d "$output_parent/.${output_name}.stage.XXXXXX")"
published=false
cleanup() {
  if [[ -n "$stage" ]]; then
    rm -rf -- "$stage"
  fi
  if [[ "$published" == true ]]; then
    rm -rf -- "$output"
  fi
}
trap cleanup EXIT

for file in "${files[@]}"; do
  source="$package/$file"
  if [[ ! -f "$source" || -L "$source" ]]; then
    echo "accepted package does not contain regular file: $file" >&2
    exit 1
  fi
  install -m 0644 "$source" "$stage/$file"
  cmp --silent "$source" "$stage/$file"
done

mv "$stage" "$output"
stage=""
published=true

for file in "${files[@]}"; do
  if [[ ! -f "$output/$file" || -L "$output/$file" ]]; then
    echo "exported package does not contain regular file: $file" >&2
    exit 1
  fi
done
(
  cd "$output"
  sha256sum --check SHA256SUMS
  node smoke.mjs
)

published=false
trap - EXIT
printf 'Illuminate v3 package exported to %s\n' "$output"
