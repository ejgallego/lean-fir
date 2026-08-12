#!/usr/bin/env bash
set -euo pipefail

git_common_dir="$(git rev-parse --path-format=absolute --git-common-dir)"
repository_root="$(cd "$git_common_dir/.." && pwd -P)"
worktree_root="$(git rev-parse --show-toplevel)"

IFS= read -r lean_toolchain < "$worktree_root/lean-toolchain"
if [[ -z "$lean_toolchain" ]]; then
  echo "lean-toolchain is empty" >&2
  exit 1
fi

# Follow Elan's readable escaping while retaining an explicit FIR-local
# toolchain boundary. Build traces still bind every artifact to Lean's commit.
cache_toolchain="${lean_toolchain//:/---}"
cache_toolchain="${cache_toolchain//\//--}"
cache_root="$repository_root/.lake_cache"
cache_dir="$cache_root/$cache_toolchain"

umask 077
install -d -m 700 -- "$cache_root" "$cache_dir"
chmod 700 -- "$cache_root" "$cache_dir"
printf '%s\n' "$cache_dir"
