#!/usr/bin/env bash
set -euo pipefail

lane_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$lane_dir" rev-parse --show-toplevel)"
deps_root="${FIR_LCNF_C_WASM_DEPS:-$repo_root/.deps/lcnf-c-wasm}"

# shellcheck source=toolchain-pins.sh
# shellcheck disable=SC1091
source "$lane_dir/toolchain-pins.sh"

usage() {
  cat <<'EOF'
usage: build-emscripten.sh [options] <entry.lean>

Build a Lean module through final LCNF, optimized C, and Emscripten Wasm.

Options:
  --export <symbol>       Export a C identifier declared with @[export].
                         May be repeated.
  --extra-source <file>  Compile and link another Lean module. May be repeated.
  --start <symbol>        Run a zero-argument IO UInt32 export after module init.
  --root <directory>      Lean source root (default: repository root).
  --out-dir <directory>  Artifact directory.
  --name <name>           Output basename (default: entry filename).
  --help                  Show this help.
EOF
}

die() {
  echo "build-emscripten.sh: $*" >&2
  exit 1
}

require_option_value() {
  local option="$1"
  local count="$2"
  if ((count < 2)); then
    die "$option requires a value"
  fi
}

validate_c_identifier() {
  local label="$1"
  local identifier="$2"
  if [[ ! "$identifier" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]]; then
    die "$label is not a C identifier: $identifier"
  fi
}

resolve_file() {
  local path="$1"
  local directory
  if [[ ! -f "$path" ]]; then
    die "Lean source does not exist: $path"
  fi
  if [[ "$path" != *.lean ]]; then
    die "Lean source must have a .lean extension: $path"
  fi
  directory="$(cd "$(dirname "$path")" && pwd)"
  printf '%s/%s\n' "$directory" "$(basename "$path")"
}

entry_source=""
lean_root="$repo_root"
out_dir=""
artifact_name=""
start_symbol=""
declare -a exported_symbols=()
declare -a extra_sources=()
declare -A seen_exports=()

while (($# > 0)); do
  case "$1" in
    --export)
      require_option_value "$1" "$#"
      validate_c_identifier "export" "$2"
      if [[ -n "${seen_exports[$2]:-}" ]]; then
        die "duplicate export: $2"
      fi
      seen_exports[$2]=1
      exported_symbols+=("$2")
      shift 2
      ;;
    --extra-source)
      require_option_value "$1" "$#"
      extra_sources+=("$2")
      shift 2
      ;;
    --start)
      require_option_value "$1" "$#"
      validate_c_identifier "start symbol" "$2"
      start_symbol="$2"
      shift 2
      ;;
    --root)
      require_option_value "$1" "$#"
      lean_root="$2"
      shift 2
      ;;
    --out-dir)
      require_option_value "$1" "$#"
      out_dir="$2"
      shift 2
      ;;
    --name)
      require_option_value "$1" "$#"
      artifact_name="$2"
      shift 2
      ;;
    --help)
      usage
      exit 0
      ;;
    -*)
      die "unknown option: $1"
      ;;
    *)
      if [[ -n "$entry_source" ]]; then
        die "only one entry module may be specified"
      fi
      entry_source="$1"
      shift
      ;;
  esac
done

if [[ -z "$entry_source" ]]; then
  usage >&2
  exit 1
fi

entry_source="$(resolve_file "$entry_source")"
for index in "${!extra_sources[@]}"; do
  extra_sources[index]="$(resolve_file "${extra_sources[index]}")"
done
if [[ ! -d "$lean_root" ]]; then
  die "Lean source root does not exist: $lean_root"
fi
lean_root="$(cd "$lean_root" && pwd)"

if [[ -z "$artifact_name" ]]; then
  artifact_name="$(basename "$entry_source" .lean)"
fi
if [[ ! "$artifact_name" =~ ^[A-Za-z0-9][A-Za-z0-9_.-]*$ ]]; then
  die "artifact name contains unsupported characters: $artifact_name"
fi
if [[ -z "$out_dir" ]]; then
  out_dir="$repo_root/_build/lcnf-c-wasm/build/$artifact_name"
fi

for tool in git grep lake node sed sha256sum; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    die "required build tool not found: $tool"
  fi
done

emsdk_dir="$deps_root/emsdk"
lean_build="$deps_root/lean4-emscripten-build"
lean_runtime="$lean_build/lib/lean/libleanrt.a"
lean_init="$lean_build/lib/lean/libInit.a"
lean_std="$lean_build/lib/lean/libStd.a"

for dependency in "$emsdk_dir/emsdk_env.sh" "$lean_runtime" "$lean_init" "$lean_std"; do
  if [[ ! -f "$dependency" ]]; then
    die "Emscripten Lean runtime is not ready; run $lane_dir/setup-emscripten.sh"
  fi
done

lean_version="$(lake -d "$repo_root" env lean --version)"
if [[ "$lean_version" != *"commit $FIR_LCNF_C_LEAN_COMMIT"* ]]; then
  die "Lean compiler does not match the pinned runtime: $lean_version"
fi

export EMSDK_QUIET=1
# shellcheck disable=SC1091
source "$emsdk_dir/emsdk_env.sh"

for tool in emcc em++; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    die "active Emscripten tool not found: $tool"
  fi
done
if [[ "$(emcc --version | head -n 1)" != *"$FIR_LCNF_C_EMSDK_VERSION"* ]]; then
  die "active Emscripten does not match pin $FIR_LCNF_C_EMSDK_VERSION"
fi

mkdir -p "$out_dir"

compile_flags=(
  -std=c11
  -O3
  -DNDEBUG
  -DLEAN_EXPORTING
  -flto
  -fomit-frame-pointer
  -ffunction-sections
  -fdata-sections
  -fvisibility=hidden
  -fno-fast-math
  -ffp-contract=off
  -fwasm-exceptions
  -pthread
  -I "$lean_build/include"
)

declare -a sources=("$entry_source" "${extra_sources[@]}")
declare -a generated_sources=()
declare -a generated_objects=()
declare -A used_stems=()

for source in "${sources[@]}"; do
  stem="$(basename "$source" .lean)"
  if [[ -n "${used_stems[$stem]:-}" ]]; then
    die "source basenames must be unique: $stem"
  fi
  used_stems[$stem]=1
  generated_c="$out_dir/$stem.c"
  generated_o="$out_dir/$stem.o"
  lake -d "$repo_root" env lean \
    -c "$generated_c" \
    -R "$lean_root" \
    "$source"
  emcc "${compile_flags[@]}" -c "$generated_c" -o "$generated_o"
  generated_sources+=("$generated_c")
  generated_objects+=("$generated_o")
done

entry_generated_c="${generated_sources[0]}"
mapfile -t module_initializers < <(
  sed -nE \
    's/^LEAN_EXPORT lean_object\* (initialize_[A-Za-z0-9_]+)\(uint8_t builtin\) \{$/\1/p' \
    "$entry_generated_c"
)
if ((${#module_initializers[@]} != 1)); then
  die "expected exactly one module initializer in $entry_generated_c"
fi
module_initializer="${module_initializers[0]}"
validate_c_identifier "module initializer" "$module_initializer"

for symbol in "${exported_symbols[@]}"; do
  if ! grep -E -q \
    "^LEAN_EXPORT .*[[:space:]*]${symbol}\\(" \
    "${generated_sources[@]}"; then
    die "generated C does not declare requested symbol: $symbol"
  fi
done
if [[ -n "$start_symbol" ]] && ! grep -E -q \
  "^LEAN_EXPORT lean_object\\* ${start_symbol}\\(\\);" \
  "${generated_sources[@]}"; then
  die "generated C does not declare zero-argument IO start symbol: $start_symbol"
fi

host_o="$out_dir/$artifact_name.module.o"
host_flags=(
  "${compile_flags[@]}"
  "-DFIR_LCNF_C_MODULE_INITIALIZER=$module_initializer"
)
if [[ -n "$start_symbol" ]]; then
  host_flags+=("-DFIR_LCNF_C_IO_START=$start_symbol")
fi
emcc \
  "${host_flags[@]}" \
  -c "$lane_dir/runtime/emscripten-module.c" \
  -o "$host_o"

exported_functions="_fir_lcnf_c_initialize"
for symbol in "${exported_symbols[@]}"; do
  exported_functions+=",_$symbol"
done

module="$out_dir/$artifact_name.mjs"
artifact="$out_dir/$artifact_name.wasm"
link_flags=(
  -O3
  -flto
  -fwasm-exceptions
  -pthread
  --no-entry
  "-Wl,--gc-sections"
  "-Wl,--strip-all"
  -sALLOW_MEMORY_GROWTH=1
  -sASSERTIONS=0
  "-sENVIRONMENT=node,web"
  -sEXPORT_ES6=1
  -sMODULARIZE=1
  -sWASM_BIGINT=1
  "-sEXPORTED_FUNCTIONS=$exported_functions"
)

em++ \
  "${generated_objects[@]}" \
  "$host_o" \
  "-Wl,--start-group" \
  "$lean_std" \
  "$lean_init" \
  "$lean_runtime" \
  "-Wl,--end-group" \
  "${link_flags[@]}" \
  -o "$module"

test -s "$module"
test -s "$artifact"
manifest="$out_dir/$artifact_name.manifest.json"
manifest_args=(
  --out "$manifest"
  --module "$module"
  --wasm "$artifact"
  --name "$artifact_name"
  --root "$lean_root"
  --entry "$entry_source"
  --initializer "$module_initializer"
  --lean-version "$FIR_LCNF_C_LEAN_VERSION"
  --lean-commit "$FIR_LCNF_C_LEAN_COMMIT"
  --emscripten-version "$FIR_LCNF_C_EMSDK_VERSION"
  --emscripten-commit "$FIR_LCNF_C_EMSDK_COMMIT"
)
for source in "${extra_sources[@]}"; do
  manifest_args+=(--extra-source "$source")
done
for symbol in "${exported_symbols[@]}"; do
  manifest_args+=(--export "$symbol")
done
if [[ -n "$start_symbol" ]]; then
  manifest_args+=(--start "$start_symbol")
fi
for flag in "${compile_flags[@]}"; do
  manifest_flag="${flag//"$lean_build"/<lean-emscripten>}"
  manifest_args+=(--compile-flag "$manifest_flag")
done
for flag in "${link_flags[@]}"; do
  manifest_args+=(--link-flag "$flag")
done
node "$lane_dir/emit-emscripten-manifest.mjs" "${manifest_args[@]}"
test -s "$manifest"
printf 'Built optimized Emscripten module %s with initializer %s\n' \
  "$artifact" \
  "$module_initializer"
sha256sum "$module" "$artifact" "$manifest"
