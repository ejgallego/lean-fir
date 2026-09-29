#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

bash "$lane_dir/test-toolchain-identity.sh"
node --test "$lane_dir/test-current-prettyM-comparator.mjs"
bash "$lane_dir/check-primary.sh"
bash "$lane_dir/check-wasi.sh"
