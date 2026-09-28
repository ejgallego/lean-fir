#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
bash "$root/tooling/talos-434/test-setup.sh"
bash "$root/tooling/talos-434/setup.sh"
mkdir -p "$root/.deps/tmp"
export TMPDIR="$root/.deps/tmp"
export LAKE_CACHE_DIR="$(bash "$root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
python3 "$root/scripts/test_validate_trusted_assumptions_profiles.py"
python3 "$root/scripts/validate_trusted_assumptions.py" \
  --profile lean-4.34.1 \
  --lean-project "$root/.deps/talos-434/project"
lake -d "$root/.deps/talos-434/project" build FirTalos.ConcreteResidentFloat
lake -d "$root/.deps/talos-434/project" build FirTalos
python3 "$root/integration/talos/check-proof-trust.py"
source "$root/tooling/talos-434/identity-checks.sh"
check_revision 0e05edbcfbb105b33e90c60b4f50e2cf193d9254 \
  "$root/.deps/talos-434/talos" Talos
check_revision d13f23b723b8a846827a245b89c10fc7d3f11612 \
  "$root/.deps/talos-434/talos/.lake/packages/mathlib" Mathlib
