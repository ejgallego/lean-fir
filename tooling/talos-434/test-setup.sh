#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
overlay="$root/tooling/talos-434"
source "$overlay/identity-checks.sh"
mkdir -p "$root/.deps"
test_dir="$(mktemp -d "$root/.deps/talos-434-setup-test.XXXXXXXX")"
trap 'rm -rf -- "$test_dir"' EXIT

expect_failure() {
  if "$@" > "$test_dir/negative.log" 2>&1; then
    echo "expected setup identity failure: $*" >&2
    exit 1
  fi
}

source_dir="$test_dir/source"
target_dir="$test_dir/target"
mkdir -p "$source_dir" "$target_dir"
printf 'theorem oldProof : True := by trivial\n' > "$source_dir/Proof.lean"
printf 'theorem removedProof : True := by trivial\n' > "$source_dir/Old.lean"
printf 'stale\n' > "$target_dir/Stale.lean"
bash "$overlay/source-mirror.sh" copy "$source_dir" "$target_dir" > /dev/null
test ! -e "$target_dir/Stale.lean"

printf 'theorem newProof : True := by exact True.intro\n' > "$source_dir/Proof.lean"
mv "$source_dir/Old.lean" "$source_dir/New.lean"
bash "$overlay/source-mirror.sh" copy "$source_dir" "$target_dir" > /dev/null
test ! -e "$target_dir/Old.lean"
cmp "$source_dir/Proof.lean" "$target_dir/Proof.lean"
cmp "$source_dir/New.lean" "$target_dir/New.lean"

real_source="$test_dir/real-source"
real_target="$test_dir/real-target"
cp -a "$root/integration/talos/FirTalos" "$real_source"
proof_file=ConcreteReuseCapacityCacheCorrectness.lean
printf '\n-- candidate W6 proof-only edit\n' >> "$real_source/$proof_file"
bash "$overlay/source-mirror.sh" copy "$real_source" "$real_target" > /dev/null
cmp "$real_source/$proof_file" "$real_target/$proof_file"

printf 'corrupt\n' > "$target_dir/Proof.lean"
expect_failure bash "$overlay/source-mirror.sh" verify "$source_dir" "$target_dir"
rg -q 'source mirror inventory/hash mismatch' "$test_dir/negative.log"

mkdir -p "$test_dir/bin"
printf '%s\n' '#!/usr/bin/env bash' \
  '/usr/bin/rsync "$@"' \
  'printf "%s\n" "source changed" >> "$FIR_TEST_SOURCE/Proof.lean"' \
  > "$test_dir/bin/rsync"
chmod +x "$test_dir/bin/rsync"
expect_failure env FIR_TEST_SOURCE="$source_dir" PATH="$test_dir/bin:$PATH" \
  bash "$overlay/source-mirror.sh" copy "$source_dir" "$target_dir"
rg -q 'source changed during mirror copy' "$test_dir/negative.log"

patch_tree="$test_dir/talos-patch-fixture"
mkdir -p "$patch_tree/interpreter"
printf '%s\n' \
  'name = "Interpreter"' \
  'version = "0.1.0"' \
  'defaultTargets = ["Interpreter"]' \
  'packagesDir = "../.lake/packages"' \
  '' \
  '[[require]]' \
  'name = "mathlib"' \
  'scope = "leanprover-community"' \
  'rev = "v4.33.0"' \
  '' \
  '[[lean_lib]]' \
  'name = "Interpreter"' \
  '' \
  '[[lean_exe]]' \
  'name = "runner"' \
  'root = "Interpreter.Runner"' \
  '' \
  '[[lean_exe]]' \
  'name = "testsuite"' \
  'root = "Interpreter.Testsuite"' > "$patch_tree/interpreter/lakefile.toml"
printf '%s\n' 'leanprover/lean4:v4.33.0' > "$patch_tree/interpreter/lean-toolchain"
git -C "$patch_tree" init -q
check_hash 582d1f169327fcb399145dfe2becbb3a7c3353958648a79308339b9c8b028a8a \
  "$patch_tree/interpreter/lakefile.toml"
check_hash 302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b \
  "$patch_tree/interpreter/lean-toolchain"
(
  cd "$patch_tree"
  git apply --check --unidiff-zero "$overlay/talos.patch"
  git apply --unidiff-zero "$overlay/talos.patch"
)
check_hash 75a680e8b6726f82caebabb184f188411c7cad72c7dcd8e6f1990112337023e4 \
  "$patch_tree/interpreter/lakefile.toml"
check_hash d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b \
  "$patch_tree/interpreter/lean-toolchain"

cp "$overlay/talos.patch" "$test_dir/talos.patch"
patch_hash="$(sha256sum "$overlay/talos.patch" | cut -d' ' -f1)"
check_hash "$patch_hash" "$test_dir/talos.patch"
printf 'changed\n' >> "$test_dir/talos.patch"
expect_failure check_hash "$patch_hash" "$test_dir/talos.patch"
rg -q 'overlay identity mismatch' "$test_dir/negative.log"

printf 'leanprover/lean4:v4.34.1\n' > "$test_dir/lean-toolchain"
check_toolchain leanprover/lean4:v4.34.1 "$test_dir/lean-toolchain"
printf 'leanprover/lean4:v4.34.0\n' > "$test_dir/lean-toolchain"
expect_failure check_toolchain leanprover/lean4:v4.34.1 "$test_dir/lean-toolchain"
rg -q 'toolchain mismatch' "$test_dir/negative.log"

for dependency in talos mathlib; do
  git -C "$test_dir" init -q "$dependency"
  git -C "$test_dir/$dependency" -c commit.gpgsign=false \
    -c user.name=FIR -c user.email=fir@example.invalid \
    commit -q --allow-empty -m pinned
  revision="$(git -C "$test_dir/$dependency" rev-parse HEAD)"
  check_revision "$revision" "$test_dir/$dependency" "$dependency"
  expect_failure check_revision 0000000000000000000000000000000000000000 \
    "$test_dir/$dependency" "$dependency"
  rg -q "$dependency revision mismatch" "$test_dir/negative.log"
done

echo "PASS Talos 4.34 source mirror and pinned identity controls"
