---
id: FIR-BUG-wasm-none-arbitrary-natural-literal
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/LowerModuleProduct.lean
regression: integration/talos/artifact/resident-literal-client.mjs
---

# Summary

Resident literal installation stops at the semantic tagged limit, although the
existing concrete runtime already represents arbitrary Naturals with canonical
little-endian limbs. The real renderer retains `2^64` as a runtime import.

## Minimal reproduction

Resident-link `.literal (.nat 18446744073709551616) .tobject` with the existing
allocator. The operation remains imported.

## Exact commands

```sh
bash integration/vbp-native-session-probe/module-product-check.sh --isolated --lower
```

## Expected semantics

Construct the exact `allocateNatural` representation: canonical `naturalLimbs`,
big-natural marker, live nonpersistent header, reference count one, checked
extent and limb count. Preserve the existing immediate/promoted representations.

## Actual behavior

Strict linking rejects a remaining non-external import. No complete renderer
module is accepted or executed.

## Proof or differential evidence

The accepted 52-module/1535-body closure has one residual runtime operation,
the `2^64` literal. `Fir.Wasm.Concrete.allocateNatural` already defines its
representation without a shared-contract change.

## Semantic impact

Missing executable literal coverage; no observed incorrect runtime result.

## Classification and triage

Generic W7 generation gap. Reject semantic tagged results for values outside
the tagged range; do not truncate to UInt64 or add a host fallback.

## Workaround

None.

## Upstream tracking

None; arbitrary-precision Naturals are supported by upstream Lean.

## Resolution and regression

`ResidentLiteral` now uses `naturalLimbs` and the existing allocation header for
values above the semantic tagged range. The Node regression passes for the
first one-limb big Nat, `2^64`, and a four-limb mixed value, checks every header
and payload word over poisoned memory, and decodes through `ConcreteHost`.
Out-of-range `.tagged` results remain rejected. Renderer relinking is checked
separately; no host execution or shared-contract change is implied.
