#!/usr/bin/env bash
# Run one project command with concise success output. Failures retain the full
# log and print its tail; set FIR_VERBOSE=1 for an unfiltered interactive run.
set -euo pipefail

if [[ $# -lt 3 || $2 != -- ]]; then
  echo "usage: quiet-run.sh LABEL -- COMMAND [ARG...]" >&2
  exit 2
fi

label=$1
shift 2

if [[ ${FIR_VERBOSE:-0} == 1 ]]; then
  exec "$@"
fi

log_dir=${FIR_TOOL_LOG_DIR:-"$PWD/.deps/tool-logs"}
mkdir -p "$log_dir"
safe_label=$(tr -cs '[:alnum:]._' '_' <<<"$label")
log=$(mktemp "$log_dir/${safe_label}.XXXXXX.log")

if "$@" >"$log" 2>&1; then
  rm -f "$log"
  printf 'PASS %s\n' "$label"
  exit 0
else
  status=$?
fi

printf 'FAIL %s (full log: %s)\n' "$label" "$log" >&2
tail -n 120 "$log" >&2 || true
exit "$status"
