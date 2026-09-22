#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
overlay="$root/tooling/talos-434"
scratch="$root/.deps/talos-434"
talos="$scratch/talos"
project="$scratch/project"
talos_rev=0e05edbcfbb105b33e90c60b4f50e2cf193d9254
mathlib_rev=85e3a25e006c35636f0e53b0e9296caca2685bc0

check_hash() {
  local actual
  actual="$(sha256sum "$2")"
  actual="${actual%% *}"
  if [[ "$actual" != "$1" ]]; then
    echo "overlay identity mismatch: $2 ($actual, expected $1)" >&2
    exit 1
  fi
}

hash_lean_tree() (
  cd "$1"
  find . -type f -name '*.lean' -print0 | sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1
)

check_hash 3d72490f4bf785799082a70b5aabb1c4f86fd3ebd56ac897aed6f96e53652a64 "$overlay/talos.patch"
check_hash b45cdb52a2573023f0b3ce8e8e2bf15c799993ee91fb511dc65cf884ef647f6f "$overlay/float-normalization.patch"
check_hash aed2e6cd0c594647d27c951936236740d6fd19ccd2e49eb6a647b0650d905c4b "$overlay/interpreter-lake-manifest.json"
check_hash 722547c0b87f68efb046c33224d4429ae7bd02df774b456709f91120505defe2 "$overlay/lake-manifest.json"
check_hash a9413e752e6d64339fcc713a312a0e7d25ff5f26ce361a0f7a7e0af2a76b9a74 "$root/integration/talos/FirTalos/ConcreteResidentFloat.lean"
check_hash f367a0809cd57630f9f907da84ba4bc91661c22b52f401f03b7922e08185c454 "$root/integration/talos/FirTalos.lean"
if [[ "$(hash_lean_tree "$root/integration/talos/FirTalos")" != 05ae89aa5c3014b13041f72606e3ba67abf9d0ede7cdb85fd2311aceb5aef2fb ]]; then
  echo "FIR Talos source tree differs from the reviewed overlay base" >&2
  exit 1
fi

if [[ ! -e "$talos/.git" ]]; then
  mkdir -p "$scratch"
  git clone --filter=blob:none --no-checkout https://github.com/cajal-technologies/talos.git "$talos"
  git -C "$talos" fetch origin "$talos_rev"
  git -C "$talos" checkout --detach "$talos_rev"
fi
if [[ "$(git -C "$talos" rev-parse HEAD)" != "$talos_rev" ]]; then
  echo "Talos checkout is not pinned at $talos_rev" >&2
  exit 1
fi

tc="$talos/interpreter/lean-toolchain"
lakefile="$talos/interpreter/lakefile.toml"
if [[ "$(sha256sum "$tc" | cut -d' ' -f1)" == 302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b &&
      "$(sha256sum "$lakefile" | cut -d' ' -f1)" == 582d1f169327fcb399145dfe2becbb3a7c3353958648a79308339b9c8b028a8a ]]; then
  git -C "$talos" apply "$overlay/talos.patch"
fi
check_hash 8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88 "$tc"
check_hash d3a81bdfc0f2c4747aace9f0a4089186557686d88f49083af57d9c60d7a3a35a "$lakefile"
cp "$overlay/interpreter-lake-manifest.json" "$talos/interpreter/lake-manifest.json"
git -C "$talos" diff --cached --quiet
while IFS= read -r -d '' changed; do
  case "$changed" in
    interpreter/lean-toolchain|interpreter/lakefile.toml|interpreter/lake-manifest.json) ;;
    *) echo "unexpected Talos source change: $changed" >&2; exit 1 ;;
  esac
done < <(git -C "$talos" diff --name-only -z)

mkdir -p "$project"
cp -a "$root/integration/talos/FirTalos" "$root/integration/talos/FirTalos.lean" "$project/"
cp "$overlay/lakefile.toml" "$overlay/lean-toolchain" "$overlay/lake-manifest.json" "$project/"
patch --batch -d "$project" -p1 -i "$overlay/float-normalization.patch"
check_hash f140b3a3e32620c8bc6d581bd649aac11bafb6f210d48b070b43bfe9c93de6cd "$project/FirTalos/ConcreteResidentFloat.lean"
if [[ "$(hash_lean_tree "$project/FirTalos")" != c259656af13935588764e1b44cb5ea62ee657ed1679fdbe212eaa38d722768e9 ]]; then
  echo "FIR Talos overlay source tree differs from the reviewed result" >&2
  exit 1
fi

if [[ -d "$talos/.lake/packages/mathlib/.git" ]]; then
  if [[ "$(git -C "$talos/.lake/packages/mathlib" rev-parse HEAD)" != "$mathlib_rev" ]]; then
    echo "Mathlib checkout is not pinned at $mathlib_rev" >&2
    exit 1
  fi
fi
if [[ "$(tr -d '\r\n' < "$project/lean-toolchain")" != leanprover/lean4:v4.34.0-rc2 ]]; then
  echo "overlay toolchain mismatch" >&2
  exit 1
fi
echo "Talos 4.34 overlay ready: Talos $talos_rev, mathlib $mathlib_rev"
