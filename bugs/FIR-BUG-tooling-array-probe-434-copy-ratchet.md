---
id: FIR-BUG-tooling-array-probe-434-copy-ratchet
status: fixed
classification: tooling-validation
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: tooling-check
first-seen: 2026-09-22
reproduction: tooling/array-probe/check.mjs
regression: tooling/array-probe/check.mjs
---

# Summary

The ordinary Array probe's shared-update allocation ratchet assumes one
copy per iteration on Lean 4.33. Lean 4.34 executes the same source with
one initial copy and reuses the new Array thereafter; the probe rejects
that smaller allocation count despite the exact returned values passing.

## Minimal reproduction

On `tooling/lean-4.34` at `7cbd297872913816f444b81239c648d753130c34`,
run `make -C tooling array-probe-check` with the pinned Binaryen directory.
For size 16 and four rounds, the test demands 800 bytes and observes 320.
The first 160 bytes are the initial Array; 160 more are allocated on the first
shared update. Round counts 1, 2, 4, 8, and 16 all use 320 bytes, while the
native-result assertion in the adapter passes for every round.

## Expected semantics

The digest is `1 + 7 * rounds`, each update preserves the value read through
the pre-update alias, and unique updates allocate no additional Array.
The 4.33 exact copy-growth ratchet should remain enforced on 4.33.

## Actual behavior and impact

All observed values and unique-update allocations match the oracle. Only the
version-pinned shared allocation count differs. This blocks tooling's 4.34
check before it can test the packaged Array probe. It is not evidence of a
semantic or ownership mismatch by itself.

## Triage

Bind the exact allocation expectation to the supported Lean toolchain:
preserve the 4.33 count and require exactly one extra copy for any positive
round count under 4.34. Unknown toolchains must fail closed. Do not weaken
value checks, raw/package comparison, or the unique-update ratchet.

## Workaround

none

## Resolution and regression

The Array-probe check now selects an exact allocation ratchet only for the
two supported Lean pins. It retains the 4.33 `rounds + 1` Array count and
requires one initial Array plus one copy for all positive round counts on
4.34; unknown pins fail closed. The value, unique-update, trap-recovery,
raw-Wasm and packaged-Wasm checks are unchanged.

`make -C tooling array-probe-check` passes both the 11,391-byte raw module
and the 6,318-byte zero-import package under 4.34. The packaged function
sidecar also verifies. A separately measured six-round diagnostic records
exact 4.34 shared allocation counts `160, 320, 320, 320, 320, 320` for
rounds `0, 1, 2, 4, 8, 16` while the native-result oracle passes.
