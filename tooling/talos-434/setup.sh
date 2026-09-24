#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
overlay="$root/tooling/talos-434"
scratch="$root/.deps/talos-434"
talos="$scratch/talos"
project="$scratch/project"
talos_rev=0e05edbcfbb105b33e90c60b4f50e2cf193d9254
mathlib_rev=85e3a25e006c35636f0e53b0e9296caca2685bc0
source "$overlay/identity-checks.sh"

check_hash 6ed9d6ea8db9a539a8278994c026c995a42534b5a3f2ec53faa41bebe4b482eb "$overlay/talos.patch"
check_hash b45cdb52a2573023f0b3ce8e8e2bf15c799993ee91fb511dc65cf884ef647f6f "$overlay/float-normalization.patch"
check_hash aed2e6cd0c594647d27c951936236740d6fd19ccd2e49eb6a647b0650d905c4b "$overlay/interpreter-lake-manifest.json"
check_hash 722547c0b87f68efb046c33224d4429ae7bd02df774b456709f91120505defe2 "$overlay/lake-manifest.json"
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
check_revision "$talos_rev" "$talos" Talos

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
check_toolchain leanprover/lean4:v4.34.0-rc2 "$project/lean-toolchain"
echo "Talos 4.34 overlay ready: Talos $talos_rev, mathlib $mathlib_rev"
