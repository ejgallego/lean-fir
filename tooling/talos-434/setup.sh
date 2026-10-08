#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
overlay="$root/tooling/talos-434"
scratch="$root/.deps/talos-434"
talos="$scratch/talos"
project="$scratch/project"
talos_rev=80644390de3ad4db3055445259a034413ae41577
mathlib_rev=d13f23b723b8a846827a245b89c10fc7d3f11612
source "$overlay/identity-checks.sh"

check_hash b45cdb52a2573023f0b3ce8e8e2bf15c799993ee91fb511dc65cf884ef647f6f "$overlay/float-normalization.patch"
check_hash 2a6ac79be3ee6f09af1ff1a0b7d6447442c2c8163e3d8369efca1a0525e3f671 "$overlay/interpreter-lake-manifest.json"
check_hash 79a0b909c97fc5a37fd95900c2c15e071f2121ab62a60fcf2e78545b87e3c8e4 "$overlay/lake-manifest.json"
float_source="$root/integration/talos/FirTalos/ConcreteResidentFloat.lean"
float_hash="$(sha256sum "$float_source" | cut -d' ' -f1)"
case "$float_hash" in
  a9413e752e6d64339fcc713a312a0e7d25ff5f26ce361a0f7a7e0af2a76b9a74|\
  f140b3a3e32620c8bc6d581bd649aac11bafb6f210d48b070b43bfe9c93de6cd) ;;
  *) echo "unreviewed ConcreteResidentFloat source: $float_hash" >&2; exit 1 ;;
esac
check_hash f367a0809cd57630f9f907da84ba4bc91661c22b52f401f03b7922e08185c454 "$root/integration/talos/FirTalos.lean"

if [[ ! -e "$talos/.git" ]]; then
  mkdir -p "$scratch"
  git clone --filter=blob:none --no-checkout https://github.com/cajal-technologies/talos.git "$talos"
  git -C "$talos" fetch origin "$talos_rev"
  git -C "$talos" checkout --detach "$talos_rev"
fi
check_pristine_revision "$talos_rev" "$talos" Talos

tc="$talos/interpreter/lean-toolchain"
lakefile="$talos/interpreter/lakefile.toml"
check_hash d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b "$tc"
check_hash 75a680e8b6726f82caebabb184f188411c7cad72c7dcd8e6f1990112337023e4 "$lakefile"
check_hash 2a6ac79be3ee6f09af1ff1a0b7d6447442c2c8163e3d8369efca1a0525e3f671 \
  "$talos/interpreter/lake-manifest.json"

mkdir -p "$project"
bash "$overlay/source-mirror.sh" copy \
  "$root/integration/talos/FirTalos" "$project/FirTalos"
cp "$root/integration/talos/FirTalos.lean" "$project/FirTalos.lean"
check_hash f367a0809cd57630f9f907da84ba4bc91661c22b52f401f03b7922e08185c454 "$project/FirTalos.lean"
cp "$overlay/lakefile.toml" "$overlay/lean-toolchain" "$overlay/lake-manifest.json" "$project/"
if [[ "$float_hash" == a9413e752e6d64339fcc713a312a0e7d25ff5f26ce361a0f7a7e0af2a76b9a74 ]]; then
  patch --batch -d "$project" -p1 -i "$overlay/float-normalization.patch"
fi
check_hash f140b3a3e32620c8bc6d581bd649aac11bafb6f210d48b070b43bfe9c93de6cd "$project/FirTalos/ConcreteResidentFloat.lean"

if [[ -d "$talos/.lake/packages/mathlib/.git" ]]; then
  check_revision "$mathlib_rev" "$talos/.lake/packages/mathlib" Mathlib
fi
check_toolchain leanprover/lean4:v4.34.1 "$project/lean-toolchain"
echo "Talos 4.34.1 overlay ready: Talos $talos_rev, mathlib $mathlib_rev"
