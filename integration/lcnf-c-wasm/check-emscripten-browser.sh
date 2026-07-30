#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
browser="${1:-${FIR_BROWSER:-google-chrome}}"
port="${FIR_LCNF_C_BROWSER_PORT:-$((18000 + $$ % 18000))}"
url="http://127.0.0.1:$port/integration/lcnf-c-wasm/check-emscripten-browser.html"

for tool in python3 curl timeout "$browser"; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required browser check tool not found: $tool" >&2
    exit 1
  fi
done

test -s "$repo_root/_build/lcnf-c-wasm/emscripten/RuntimeSmoke.mjs"
test -s "$repo_root/_build/lcnf-c-wasm/emscripten/RuntimeSmoke.wasm"
test -s "$repo_root/_build/lcnf-c-wasm/emscripten/RuntimeSmoke.manifest.json"

python3 "$lane_dir/serve-browser.py" "$port" "$repo_root" \
  >/dev/null 2>&1 &
server_pid=$!

cleanup() {
  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
}
trap cleanup EXIT

for _ in {1..50}; do
  if curl --fail --silent --output /dev/null "$url"; then
    break
  fi
  sleep 0.1
done
curl --fail --silent --output /dev/null "$url"

browser_dom="$(
  timeout 30s "$browser" \
    --headless=new \
    --disable-gpu \
    --no-sandbox \
    --virtual-time-budget=15000 \
    --dump-dom \
    "$url" \
    2>/dev/null
)"
if [[ "$browser_dom" != *'data-result="pass"'* ]]; then
  printf '%s\n' "$browser_dom" >&2
  exit 1
fi

printf 'PASS Emscripten full Init/Std browser profile (%s)\n' "$browser"
