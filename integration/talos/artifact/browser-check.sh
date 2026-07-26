#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
browser="${1:-${FIR_BROWSER:-google-chrome}}"
port="${FIR_BROWSER_PORT:-$((18000 + $$ % 18000))}"
debug_port=$((port + 1))
url="http://127.0.0.1:$port/integration/talos/artifact/browser-pretty-format.html"
chrome_data="$(mktemp -d)"

test -s "$here/_build/resident-get-tag.wasm"
test -s "$here/_build/resident-get-tag.wasm.json"
test -s "$here/_build/resident-is-shared.wasm"
test -s "$here/_build/resident-is-shared.wasm.json"
test -s "$here/_build/resident-read-projections.wasm"
test -s "$here/_build/resident-read-projections.wasm.json"
test -s "$here/_build/resident-closure-projections.wasm"
test -s "$here/_build/resident-closure-projections.wasm.json"
test -s "$here/_build/resident-closure-matches.wasm"
test -s "$here/_build/resident-closure-matches.wasm.json"
test -s "$here/_build/resident-allocator.wasm"
test -s "$here/_build/resident-allocator.wasm.json"
test -s "$here/_build/source-pretty-format-resident-get-tag.wasm"
test -s "$here/_build/source-pretty-format-resident-get-tag.wasm.json"
test -s "$here/_build/source-pretty-format-resident-runtime.wasm"
test -s "$here/_build/source-pretty-format-resident-runtime.wasm.json"
test -s "$here/_build/source-pretty-format-resident-projections.wasm"
test -s "$here/_build/source-pretty-format-resident-projections.wasm.json"
test -s "$here/_build/source-pretty-format-resident-closure-projections.wasm"
test -s "$here/_build/source-pretty-format-resident-closure-projections.wasm.json"
test -s "$here/_build/source-pretty-format-resident-closure-matches.wasm"
test -s "$here/_build/source-pretty-format-resident-closure-matches.wasm.json"
test -s "$here/_build/source-pretty-format-resident-allocator.wasm"
test -s "$here/_build/source-pretty-format-resident-allocator.wasm.json"

python3 -m http.server "$port" --bind 127.0.0.1 --directory "$root" \
  >/dev/null 2>&1 &
server_pid=$!

chrome_pid=""
cleanup() {
  if [[ -n "$chrome_pid" ]]; then
    kill "$chrome_pid" 2>/dev/null || true
    wait "$chrome_pid" 2>/dev/null || true
  fi
  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  rm -rf "$chrome_data"
}
trap cleanup EXIT

for _ in {1..50}; do
  if curl --fail --silent --output /dev/null "$url"; then
    break
  fi
  sleep 0.1
done
curl --fail --silent --output /dev/null "$url"

$browser --headless=new --disable-gpu --no-sandbox \
  --remote-debugging-port="$debug_port" --user-data-dir="$chrome_data" \
  "$url" >/dev/null 2>&1 &
chrome_pid=$!

node "$here/wait-browser-result.mjs" "http://127.0.0.1:$debug_port" "$url"
echo "PASS browser Worker Fetch prettyM client ($browser)"
