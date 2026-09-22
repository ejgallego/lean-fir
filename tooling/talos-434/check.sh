#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
bash "$root/tooling/talos-434/setup.sh"
mkdir -p "$root/.deps/tmp"
export TMPDIR="$root/.deps/tmp"
export LAKE_CACHE_DIR="$(bash "$root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
python3 "$root/scripts/test_validate_trusted_assumptions_profiles.py"
python3 "$root/scripts/validate_trusted_assumptions.py" \
  --profile lean-4.34-rc2 \
  --lean-project "$root/.deps/talos-434/project"
lake -d "$root/.deps/talos-434/project" build FirTalos.ConcreteResidentFloat
lake -d "$root/.deps/talos-434/project" build FirTalos
