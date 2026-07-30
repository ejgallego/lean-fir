#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
run_id="$(date -u +%Y%m%dT%H%M%SZ)-$$"
out_root="${FIR_LCNF_C_WASM_PERF_OUT:-$repo_root/_build/lcnf-c-wasm/performance/$run_id}"
artifact_dir="$out_root/artifacts"
report_dir="$out_root/report"
passes="${FIR_LCNF_C_WASM_PERF_PASSES:-6}"
warmups="${FIR_LCNF_C_WASM_PERF_WARMUPS:-1}"
steady_rounds="${FIR_LCNF_C_WASM_PERF_ROUNDS:-4096}"
steady_iterations="${FIR_LCNF_C_WASM_PERF_ITERATIONS:-128}"
steady_warmup_iterations="${FIR_LCNF_C_WASM_PERF_IN_PROCESS_WARMUPS:-4}"
seed="${FIR_LCNF_C_WASM_PERF_SEED:-1311768467463790320}"

die() {
  echo "benchmark.sh: $*" >&2
  exit 1
}

for tool in cc date git lake node; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    die "required benchmark tool not found: $tool"
  fi
done
if [[ -e "$out_root" ]]; then
  die "refusing to overwrite performance evidence: $out_root"
fi
mkdir -p "$artifact_dir"

node "$lane_dir/test-benchmark-report.mjs"

"$lane_dir/build-emscripten.sh" \
  --root "$lane_dir" \
  --out-dir "$artifact_dir" \
  --name RuntimeSmoke \
  --export fir_lcnf_c_runtime_checksum \
  "$lane_dir/RuntimeSmoke.lean"

generated_c="$artifact_dir/RuntimeSmoke.c"
native_generated_o="$artifact_dir/RuntimeSmoke.native.o"
native_host_o="$artifact_dir/native-benchmark.o"
native_executable="$artifact_dir/RuntimeSmoke.native-benchmark"
manifest="$artifact_dir/RuntimeSmoke.manifest.json"
lean_prefix="$(lake env lean --print-prefix)"
native_generated_flags=(
  -O3
  -DNDEBUG
  -flto
  -fomit-frame-pointer
  -ffunction-sections
  -fdata-sections
  -fno-fast-math
  -ffp-contract=off
)
native_host_flags=(
  -std=c11
  -O3
  -DNDEBUG
  -fomit-frame-pointer
  -ffunction-sections
  -fdata-sections
  -fno-fast-math
  -ffp-contract=off
  -Wall
  -Wextra
  -Werror
  -I
  "$lean_prefix/include"
)
native_link_flags=(
  -O3
  -flto
  "-Wl,--gc-sections"
  -s
)

lake env leanc \
  "${native_generated_flags[@]}" \
  -c "$generated_c" \
  -o "$native_generated_o"
cc \
  "${native_host_flags[@]}" \
  -c "$lane_dir/runtime/native-benchmark.c" \
  -o "$native_host_o"
lake env leanc \
  "${native_link_flags[@]}" \
  "$native_generated_o" \
  "$native_host_o" \
  -o "$native_executable"

benchmark_args=(
  --manifest "$manifest"
  --native "$native_executable"
  --out-dir "$report_dir"
  --warmups "$warmups"
  --passes "$passes"
  --steady-rounds "$steady_rounds"
  --steady-iterations "$steady_iterations"
  --steady-warmup-iterations "$steady_warmup_iterations"
  --seed "$seed"
  --artifact "$lane_dir/RuntimeSmoke.lean"
  --artifact "$lane_dir/build-emscripten.sh"
  --artifact "$lane_dir/emit-emscripten-manifest.mjs"
  --artifact "$lane_dir/emscripten-loader.mjs"
  --artifact "$lane_dir/benchmark.sh"
  --artifact "$lane_dir/benchmark-report.mjs"
  --artifact "$lane_dir/wasm-memory.mjs"
  --artifact "$lane_dir/runtime/native-benchmark.c"
  --artifact "$generated_c"
)
for flag in "${native_generated_flags[@]}"; do
  benchmark_args+=(--native-generated-flag "$flag")
done
for flag in "${native_host_flags[@]}"; do
  benchmark_args+=(--native-host-flag "$flag")
done
for flag in "${native_link_flags[@]}"; do
  benchmark_args+=(--native-link-flag "$flag")
done
node "$lane_dir/benchmark.mjs" "${benchmark_args[@]}"

printf 'Preserved LCNF C/Wasm performance evidence in %s\n' "$out_root"
