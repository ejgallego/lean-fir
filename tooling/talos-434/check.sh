#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
bash "$root/tooling/talos-434/setup.sh"
mkdir -p "$root/.deps/tmp"
export TMPDIR="$root/.deps/tmp"
export LAKE_CACHE_DIR="$(bash "$root/scripts/fir-lake-cache-path.sh")"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
lake -d "$root/.deps/talos-434/project" build FirTalos.ConcreteResidentFloat
lake -d "$root/.deps/talos-434/project" build FirTalos
