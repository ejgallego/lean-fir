#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

bash "$lane_dir/check.sh"
bash "$lane_dir/check-emscripten.sh"
bash "$lane_dir/check-wasi.sh"
