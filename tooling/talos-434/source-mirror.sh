#!/usr/bin/env bash
set -euo pipefail

mode="${1:-}"
source_dir="${2:-}"
target_dir="${3:-}"
if [[ "$mode" != copy && "$mode" != verify ]] ||
    [[ -z "$source_dir" || -z "$target_dir" || ! -d "$source_dir" ]]; then
  echo "usage: source-mirror.sh {copy|verify} SOURCE_DIR TARGET_DIR" >&2
  exit 2
fi

tree_digest() (
  cd "$1"
  if [[ -n "$(find . -type l -print -quit)" ]]; then
    echo "source mirror contains a symlink: $1" >&2
    exit 1
  fi
  find . -type f -print0 | sort -z | xargs -0 -r sha256sum | sha256sum | cut -d' ' -f1
)

before="$(tree_digest "$source_dir")"
if [[ "$mode" == copy ]]; then
  mkdir -p "$target_dir"
  rsync -a --delete -- "$source_dir/" "$target_dir/"
fi
if [[ ! -d "$target_dir" ]]; then
  echo "source mirror missing target: $target_dir" >&2
  exit 1
fi
after="$(tree_digest "$source_dir")"
copied="$(tree_digest "$target_dir")"
if [[ "$before" != "$after" ]]; then
  echo "source changed during mirror copy: $source_dir" >&2
  exit 1
fi
if [[ "$after" != "$copied" ]]; then
  echo "source mirror inventory/hash mismatch: $source_dir -> $target_dir" >&2
  exit 1
fi
printf '%s\n' "$copied"
