#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
destination="$repo_root/.deps/talos"
revision="0e05edbcfbb105b33e90c60b4f50e2cf193d9254"

if [[ ! -d "$destination/.git" ]]; then
  mkdir -p "$repo_root/.deps"
  git clone https://github.com/cajal-technologies/talos.git "$destination"
fi

git -C "$destination" fetch origin "$revision"
git -C "$destination" checkout --detach "$revision"

actual="$(git -C "$destination" rev-parse HEAD)"
if [[ "$actual" != "$revision" ]]; then
  echo "Talos revision mismatch: expected $revision, found $actual" >&2
  exit 1
fi

toolchain="$(tr -d '\r\n' < "$destination/interpreter/lean-toolchain")"
if [[ "$toolchain" != "leanprover/lean4:v4.33.0" ]]; then
  echo "Talos toolchain mismatch: expected Lean 4.33.0, found $toolchain" >&2
  exit 1
fi

echo "Talos ready at $revision"
