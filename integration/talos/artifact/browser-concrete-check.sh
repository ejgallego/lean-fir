#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
browser="${1:-${FIR_BROWSER:-google-chrome}}"
corpus_path="${2:-_build/concrete-corpus}"
port="${FIR_BROWSER_CONCRETE_PORT:-$((18000 + $$ % 18000))}"
debug_port=$((port + 1))
if [[ ! "$corpus_path" =~ ^_build/[A-Za-z0-9._/-]+$ ]] || \
    [[ "/$corpus_path/" == *"/../"* ]]; then
  echo "corpus path must be repository-local artifact _build data" >&2
  exit 2
fi
url="http://127.0.0.1:$port/integration/talos/artifact/browser-concrete.html?corpus=$corpus_path"
chrome_data="$(mktemp -d)"

test -s "$here/$corpus_path/literal.wasm"
test -s "$here/$corpus_path/literal.wasm.json"
test -s "$here/$corpus_path/literal.expected.json"
test -s "$here/_build/source-nat-list-case.wasm"
test -s "$here/_build/source-nat-list-case.wasm.json"
test -s "$here/_build/source-string-input.wasm"
test -s "$here/_build/source-string-input.wasm.json"
test -s "$here/_build/source-pretty-format-module.wasm"
test -s "$here/_build/source-pretty-format-module.wasm.json"

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

node "$here/wait-browser-result.mjs" \
  "http://127.0.0.1:$debug_port" "$url" 120
echo "PASS browser concrete Wasm artifacts ($browser)"
