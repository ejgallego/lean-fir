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

cp "$overlay/talos.patch" "$test_dir/talos.patch"
patch_hash="$(sha256sum "$overlay/talos.patch" | cut -d' ' -f1)"
check_hash "$patch_hash" "$test_dir/talos.patch"
printf 'changed\n' >> "$test_dir/talos.patch"
expect_failure check_hash "$patch_hash" "$test_dir/talos.patch"
rg -q 'overlay identity mismatch' "$test_dir/negative.log"

printf 'leanprover/lean4:v4.34.0-rc2\n' > "$test_dir/lean-toolchain"
check_toolchain leanprover/lean4:v4.34.0-rc2 "$test_dir/lean-toolchain"
printf 'leanprover/lean4:v4.34.0\n' > "$test_dir/lean-toolchain"
expect_failure check_toolchain leanprover/lean4:v4.34.0-rc2 "$test_dir/lean-toolchain"
rg -q 'toolchain mismatch' "$test_dir/negative.log"

for dependency in talos mathlib; do
  git -C "$test_dir" init -q "$dependency"
  git -C "$test_dir/$dependency" -c user.name=FIR -c user.email=fir@example.invalid \
    commit -q --allow-empty -m pinned
  revision="$(git -C "$test_dir/$dependency" rev-parse HEAD)"
  check_revision "$revision" "$test_dir/$dependency" "$dependency"
  expect_failure check_revision 0000000000000000000000000000000000000000 \
    "$test_dir/$dependency" "$dependency"
  rg -q "$dependency revision mismatch" "$test_dir/negative.log"
done

echo "PASS Talos 4.34 source mirror and pinned identity controls"
