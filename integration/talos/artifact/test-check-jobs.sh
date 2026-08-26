#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
source "$here/check-jobs.sh"

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

record_success() {
  printf '%s\n' "$1" > "$1"
}

fir_run_producer_pair 2 record_success "$scratch/parallel-a" \
  "$scratch/parallel-b"
test -f "$scratch/parallel-a"
test -f "$scratch/parallel-b"

record_order() {
  printf '%s\n' "$1" >> "$scratch/order"
}

fir_run_producer_pair 1 record_order first second
test "$(sed -n '1p' "$scratch/order")" = first
test "$(sed -n '2p' "$scratch/order")" = second

fail_one() {
  if [[ "$1" == fail ]]; then
    return 17
  fi
  printf '%s\n' "$1" > "$scratch/completed-peer"
}

if fir_run_producer_pair 2 fail_one fail completed; then
  echo "failing producer pair unexpectedly succeeded" >&2
  exit 1
fi
test "$(cat "$scratch/completed-peer")" = completed

if fir_run_producer_pair 1 fail_one fail completed; then
  echo "failing serial producer pair unexpectedly succeeded" >&2
  exit 1
fi
test "$(cat "$scratch/completed-peer")" = completed

echo "artifact producer-pair checks passed"
