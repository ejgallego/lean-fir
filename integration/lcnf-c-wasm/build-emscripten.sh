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
  --extra-c-source <file>
                         Compile and link a C bridge. May be repeated.
  --heap-view             Expose Module.HEAPU8 for bulk bridge transfers.
  --start <symbol>        Run a zero-argument IO UInt32 export after module init.
  --root <directory>      Lean source root (default: repository root).
  --out-dir <directory>  Artifact directory.
  --name <name>           Output basename (default: entry filename).
  --rebuild               Rebuild every compilation and link stage.
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

resolve_c_file() {
  local path="$1"
  local directory
  if [[ ! -f "$path" ]]; then
    die "C source does not exist: $path"
  fi
  if [[ "$path" != *.c ]]; then
    die "C source must have a .c extension: $path"
  fi
  directory="$(cd "$(dirname "$path")" && pwd)"
  printf '%s/%s\n' "$directory" "$(basename "$path")"
}

file_digest() {
  local digest_line
  digest_line="$(sha256sum "$1")"
  printf '%s\n' "${digest_line%% *}"
}

hash_key() {
  local digest_line
  digest_line="$(sha256sum)"
  printf '%s\n' "${digest_line%% *}"
}

key_field() {
  printf '%s\0%s\0' "$1" "$2"
}

emscripten_environment_key() {
  key_field environment-mode isolated-v1
  key_field EM_CONFIG "$emscripten_config"
  key_field EM_CONFIG-sha256 "$emscripten_config_digest"
  key_field EM_CACHE "$emscripten_cache"
  key_field EMSDK "$emsdk_dir"
  key_field EMSDK_PYTHON "$emsdk_python_tool"
  key_field EMSDK_PYTHON-sha256 "$emsdk_python_tool_digest"
  key_field EMSDK_NODE "$emsdk_node_tool"
  key_field EMSDK_NODE-sha256 "$emsdk_node_tool_digest"
  key_field PATH "$emscripten_path"
  key_field LANG C
  key_field LC_ALL C
}

run_emcc() {
  env "${emscripten_env[@]}" "$emcc_tool" "$@"
}

run_emxx() {
  env "${emscripten_env[@]}" "$emxx_tool" "$@"
}

cache_hit() {
  local stage="$1"
  local expected_key="$2"
  shift 2
  local key_file="$cache_dir/$stage.key"
  local digests_file="$cache_dir/$stage.digests"
  local stored_key
  local index
  local actual_digest
  local -a outputs=("$@")
  local -a stored_digests=()

  if ((rebuild)) || [[ ! -f "$key_file" || ! -f "$digests_file" ]]; then
    return 1
  fi
  IFS= read -r stored_key < "$key_file" || return 1
  [[ "$stored_key" == "$expected_key" ]] || return 1
  mapfile -t stored_digests < "$digests_file"
  ((${#stored_digests[@]} == ${#outputs[@]})) || return 1
  for index in "${!stored_digests[@]}"; do
    [[ "${stored_digests[index]}" =~ ^[0-9a-f]{64}$ ]] || return 1
    [[ -s "${outputs[index]}" ]] || return 1
    actual_digest="$(file_digest "${outputs[index]}")"
    [[ "$actual_digest" == "${stored_digests[index]}" ]] || return 1
  done
}

record_cache() {
  local stage="$1"
  local key="$2"
  shift 2
  local key_tmp
  local digests_tmp
  local output

  key_tmp="$(mktemp "$cache_dir/.key.XXXXXX")"
  digests_tmp="$(mktemp "$cache_dir/.digests.XXXXXX")"
  printf '%s\n' "$key" > "$key_tmp"
  for output in "$@"; do
    file_digest "$output" >> "$digests_tmp"
  done
  mv -f "$digests_tmp" "$cache_dir/$stage.digests"
  mv -f "$key_tmp" "$cache_dir/$stage.key"
}

object_key() {
  local kind="$1"
  local source="$2"
  shift 2
  local index=0
  local flag
  {
    key_field cache-format fir-lcnf-c-wasm-v1
    key_field stage "$kind"
    key_field source "$source"
    key_field source-sha256 "$(file_digest "$source")"
    key_field emcc "$emcc_tool"
    key_field emcc-sha256 "$emcc_tool_digest"
    key_field emcc-version "$emcc_version"
    key_field emscripten-version "$FIR_LCNF_C_EMSDK_VERSION"
    key_field emscripten-commit "$FIR_LCNF_C_EMSDK_COMMIT"
    emscripten_environment_key
    key_field lean-include-tree-sha256 "$lean_include_tree_digest"
    key_field compile-mode -c
    for flag in "$@"; do
      key_field "flag.$index" "$flag"
      index=$((index + 1))
    done
  } | hash_key
}

entry_source=""
lean_root="$repo_root"
out_dir=""
artifact_name=""
start_symbol=""
heap_view=0
rebuild=0
declare -a exported_symbols=()
declare -a extra_sources=()
declare -a extra_c_sources=()
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
    --extra-c-source)
      require_option_value "$1" "$#"
      extra_c_sources+=("$2")
      shift 2
      ;;
    --heap-view)
      heap_view=1
      shift
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
    --rebuild)
      rebuild=1
      shift
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
for index in "${!extra_c_sources[@]}"; do
  extra_c_sources[index]="$(resolve_c_file "${extra_c_sources[index]}")"
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

for tool in env find git grep lake mktemp mv node python3 rm sed sha256sum sort; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    die "required build tool not found: $tool"
  fi
done

emsdk_dir="$deps_root/emsdk"
lean_build="$deps_root/lean4-emscripten-build"
lean_runtime="$lean_build/lib/lean/libleanrt.a"
lean_init="$lean_build/lib/lean/libInit.a"
lean_std="$lean_build/lib/lean/libStd.a"
lean_include="$lean_build/include"

for dependency in "$emsdk_dir/emsdk_env.sh" "$lean_runtime" "$lean_init" "$lean_std"; do
  if [[ ! -f "$dependency" ]]; then
    die "Emscripten Lean runtime is not ready; run $lane_dir/setup-emscripten.sh"
  fi
done
if [[ ! -f "$lean_include/lean/lean.h" ]]; then
  die "Emscripten Lean headers are not ready; run $lane_dir/setup-emscripten.sh"
fi

lean_version="$(lake -d "$repo_root" env lean --version)"
if [[ "$lean_version" != *"commit $FIR_LCNF_C_LEAN_COMMIT"* ]]; then
  die "Lean compiler does not match the pinned runtime: $lean_version"
fi
lean_prefix="$(lake -d "$repo_root" env lean --print-prefix)"
lean_tool="$lean_prefix/bin/lean"
if [[ ! -x "$lean_tool" ]]; then
  die "Lean compiler binary is not executable: $lean_tool"
fi
lean_tool_digest="$(file_digest "$lean_tool")"
lake_version="$(lake --version)"

export EMSDK_QUIET=1
# shellcheck disable=SC1091
source "$emsdk_dir/emsdk_env.sh"

emcc_tool="$emsdk_dir/upstream/emscripten/emcc"
emxx_tool="$emsdk_dir/upstream/emscripten/em++"
emsdk_python_tool="$(command -v python3)"
emsdk_node_tool="${EMSDK_NODE:-}"
emscripten_config="$emsdk_dir/.emscripten"
emscripten_cache="$emsdk_dir/upstream/emscripten/cache"
for dependency in \
    "$emcc_tool" \
    "$emxx_tool" \
    "$emsdk_python_tool" \
    "$emsdk_node_tool" \
    "$emscripten_config"; do
  if [[ ! -f "$dependency" ]]; then
    die "pinned Emscripten environment dependency not found: $dependency"
  fi
done
if [[ ! -d "$emscripten_cache" ]]; then
  die "pinned Emscripten cache not found: $emscripten_cache"
fi
emscripten_path="$(dirname "$emcc_tool"):$(dirname "$emsdk_python_tool"):/usr/bin:/bin"
# emcc accepts flags and tool/config overrides from the ambient environment.
# Isolate it so the cache key below accounts for every retained value.
declare -a emscripten_env=(
  -i
  "EMSDK=$emsdk_dir"
  "EMSDK_NODE=$emsdk_node_tool"
  "EMSDK_PYTHON=$emsdk_python_tool"
  EMSDK_QUIET=1
  "EM_CONFIG=$emscripten_config"
  "EM_CACHE=$emscripten_cache"
  "PATH=$emscripten_path"
  LANG=C
  LC_ALL=C
)
emcc_version="$(run_emcc --version | head -n 1)"
emxx_version="$(run_emxx --version | head -n 1)"
if [[ "$emcc_version" != *"$FIR_LCNF_C_EMSDK_VERSION"* ]]; then
  die "active Emscripten does not match pin $FIR_LCNF_C_EMSDK_VERSION"
fi
emcc_tool_digest="$(file_digest "$emcc_tool")"
emxx_tool_digest="$(file_digest "$emxx_tool")"
emscripten_config_digest="$(file_digest "$emscripten_config")"
emsdk_python_tool_digest="$(file_digest "$emsdk_python_tool")"
emsdk_node_tool_digest="$(file_digest "$emsdk_node_tool")"
lean_include_tree_digest="$({
  while IFS= read -r -d '' header; do
    relative_header="${header#"$lean_include"/}"
    key_field path "$relative_header"
    key_field sha256 "$(file_digest "$header")"
  done < <(
    find "$lean_include" \( -type f -o -type l \) -print0 |
      LC_ALL=C sort -z
  )
} | hash_key)"

mkdir -p "$out_dir"
cache_dir="$out_dir/.fir-emscripten-cache/$artifact_name"
mkdir -p "$cache_dir"
build_tmp="$(mktemp -d "$out_dir/.fir-emscripten-build.XXXXXX")"
cleanup() {
  rm -rf "$build_tmp"
}
trap cleanup EXIT

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
declare -a extra_c_objects=()
declare -A used_stems=()

for source_index in "${!sources[@]}"; do
  source="${sources[source_index]}"
  stem="$(basename "$source" .lean)"
  if [[ -n "${used_stems[$stem]:-}" ]]; then
    die "source basenames must be unique: $stem"
  fi
  used_stems[$stem]=1
  generated_c="$out_dir/$stem.c"
  generated_o="$out_dir/$stem.o"
  deps_snapshot="$build_tmp/lean-$source_index.deps"
  lake -d "$repo_root" env lean \
    --deps \
    -R "$lean_root" \
    "$source" > "$deps_snapshot"
  dependency_index=0
  lean_key="$({
    key_field cache-format fir-lcnf-c-wasm-v1
    key_field stage lean-to-c
    key_field source "$source"
    key_field source-sha256 "$(file_digest "$source")"
    key_field dependency-list-sha256 "$(file_digest "$deps_snapshot")"
    while IFS= read -r dependency; do
      [[ -f "$dependency" ]] || die "Lean dependency does not exist: $dependency"
      key_field "dependency.$dependency_index.path" "$dependency"
      key_field "dependency.$dependency_index.sha256" "$(file_digest "$dependency")"
      dependency_index=$((dependency_index + 1))
    done < "$deps_snapshot"
    key_field repo-root "$repo_root"
    key_field lean-root "$lean_root"
    key_field option.0 -c
    key_field option.1 -R
    key_field lean "$lean_tool"
    key_field lean-sha256 "$lean_tool_digest"
    key_field lean-version "$lean_version"
    key_field lean-pinned-version "$FIR_LCNF_C_LEAN_VERSION"
    key_field lean-pinned-commit "$FIR_LCNF_C_LEAN_COMMIT"
    key_field lake-version "$lake_version"
  } | hash_key)"
  lean_stage="lean-$source_index"
  if cache_hit "$lean_stage" "$lean_key" "$generated_c"; then
    printf 'HIT lean-c %s\n' "$stem"
  else
    printf 'BUILD lean-c %s\n' "$stem"
    generated_c_tmp="$build_tmp/$stem.c"
    lake -d "$repo_root" env lean \
      -c "$generated_c_tmp" \
      -R "$lean_root" \
      "$source"
    test -s "$generated_c_tmp"
    mv -f "$generated_c_tmp" "$generated_c"
    record_cache "$lean_stage" "$lean_key" "$generated_c"
  fi
  generated_object_key="$(object_key generated-lean-c "$generated_c" \
    "${compile_flags[@]}")"
  generated_object_stage="generated-object-$source_index"
  if cache_hit "$generated_object_stage" "$generated_object_key" "$generated_o"; then
    printf 'HIT c-object %s\n' "$stem"
  else
    printf 'BUILD c-object %s\n' "$stem"
    generated_o_tmp="$build_tmp/generated-$source_index.o"
    run_emcc "${compile_flags[@]}" -c "$generated_c" -o "$generated_o_tmp"
    test -s "$generated_o_tmp"
    mv -f "$generated_o_tmp" "$generated_o"
    record_cache "$generated_object_stage" "$generated_object_key" "$generated_o"
  fi
  generated_sources+=("$generated_c")
  generated_objects+=("$generated_o")
done

for index in "${!extra_c_sources[@]}"; do
  source="${extra_c_sources[index]}"
  object="$out_dir/$artifact_name.bridge.$index.o"
  bridge_key="$(object_key extra-c "$source" "${compile_flags[@]}")"
  bridge_stage="bridge-object-$index"
  if cache_hit "$bridge_stage" "$bridge_key" "$object"; then
    printf 'HIT c-object bridge[%s]\n' "$index"
  else
    printf 'BUILD c-object bridge[%s]\n' "$index"
    object_tmp="$build_tmp/bridge-$index.o"
    run_emcc "${compile_flags[@]}" -c "$source" -o "$object_tmp"
    test -s "$object_tmp"
    mv -f "$object_tmp" "$object"
    record_cache "$bridge_stage" "$bridge_key" "$object"
  fi
  extra_c_objects+=("$object")
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
    "${generated_sources[@]}" "${extra_c_sources[@]}"; then
    die "generated Lean/C sources do not declare requested symbol: $symbol"
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
host_source="$lane_dir/runtime/emscripten-module.c"
host_key="$(object_key host "$host_source" "${host_flags[@]}")"
if cache_hit host-object "$host_key" "$host_o"; then
  printf 'HIT c-object host\n'
else
  printf 'BUILD c-object host\n'
  host_o_tmp="$build_tmp/host.o"
  run_emcc \
    "${host_flags[@]}" \
    -c "$host_source" \
    -o "$host_o_tmp"
  test -s "$host_o_tmp"
  mv -f "$host_o_tmp" "$host_o"
  record_cache host-object "$host_key" "$host_o"
fi

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
if ((heap_view)); then
  link_flags+=("-sEXPORTED_RUNTIME_METHODS=HEAPU8")
fi

link_key="$({
  key_field cache-format fir-lcnf-c-wasm-v1
  key_field stage link
  key_field artifact-name "$artifact_name"
  key_field emxx "$emxx_tool"
  key_field emxx-sha256 "$emxx_tool_digest"
  key_field emxx-version "$emxx_version"
  key_field emscripten-version "$FIR_LCNF_C_EMSDK_VERSION"
  key_field emscripten-commit "$FIR_LCNF_C_EMSDK_COMMIT"
  emscripten_environment_key
  link_input_index=0
  for link_input in \
      "${generated_objects[@]}" \
      "${extra_c_objects[@]}" \
      "$host_o" \
      "$lean_std" \
      "$lean_init" \
      "$lean_runtime"; do
    key_field "input.$link_input_index.path" "$link_input"
    key_field "input.$link_input_index.sha256" "$(file_digest "$link_input")"
    link_input_index=$((link_input_index + 1))
  done
  link_flag_index=0
  for flag in "${link_flags[@]}"; do
    key_field "flag.$link_flag_index" "$flag"
    link_flag_index=$((link_flag_index + 1))
  done
  key_field group-start "-Wl,--start-group"
  key_field group-end "-Wl,--end-group"
} | hash_key)"
if cache_hit link "$link_key" "$module" "$artifact"; then
  printf 'HIT link %s\n' "$artifact_name"
else
  printf 'BUILD link %s\n' "$artifact_name"
  link_tmp_dir="$build_tmp/link"
  mkdir -p "$link_tmp_dir"
  module_tmp="$link_tmp_dir/$artifact_name.mjs"
  artifact_tmp="$link_tmp_dir/$artifact_name.wasm"
  run_emxx \
    "${generated_objects[@]}" \
    "${extra_c_objects[@]}" \
    "$host_o" \
    "-Wl,--start-group" \
    "$lean_std" \
    "$lean_init" \
    "$lean_runtime" \
    "-Wl,--end-group" \
    "${link_flags[@]}" \
    -o "$module_tmp"
  test -s "$module_tmp"
  test -s "$artifact_tmp"
  mv -f "$module_tmp" "$module"
  mv -f "$artifact_tmp" "$artifact"
  record_cache link "$link_key" "$module" "$artifact"
fi

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
for source in "${extra_c_sources[@]}"; do
  manifest_args+=(--extra-c-source "$source")
done
for symbol in "${exported_symbols[@]}"; do
  manifest_args+=(--export "$symbol")
done
if ((heap_view)); then
  manifest_args+=(--runtime-method HEAPU8)
fi
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
printf 'BUILD manifest %s\n' "$artifact_name"
node "$lane_dir/emit-emscripten-manifest.mjs" "${manifest_args[@]}"
test -s "$manifest"
printf 'Built optimized Emscripten module %s with initializer %s\n' \
  "$artifact" \
  "$module_initializer"
sha256sum "$module" "$artifact" "$manifest"
