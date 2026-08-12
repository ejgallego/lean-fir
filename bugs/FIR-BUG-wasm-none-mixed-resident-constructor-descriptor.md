---
id: FIR-BUG-wasm-none-mixed-resident-constructor-descriptor
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-13
reproduction: integration/talos/artifact/call-concrete-pretty-format.mjs
regression: integration/talos/artifact/test-concrete-initial-runtime.mjs
---

# Summary

The mixed resident/host concrete runtime rejects a constructor mutation when
Wasm allocated the constructor and the still-imported JavaScript setter did
not observe that allocation.

## Minimal reproduction

Generate the pretty-format checkpoint that internalizes constructor
allocation while retaining object setters, then call the real structured
pretty-format entry through the concrete host.

## Exact commands

```sh
cd integration/talos/artifact
FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 ./check.sh
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-constructors.wasm
```

The second command is sufficient after the checkpoint artifacts exist.

## Expected semantics

Resident constructor allocation and imported object mutation share the same
concrete memory and header layout. The host setter should accept a live
constructor address allocated below the synchronized resident frontier and
write the requested object slot.

## Actual behavior

`ConcreteHost.objectSet` finds a valid live constructor header but aborts
because its validation-only `descriptors` map contains entries only for
objects allocated by the host:

```text
WasmAssertionError: missing concrete constructor descriptor
```

## Proof or differential evidence

The fully imported concrete pretty-format module and the fully resident
module both return the native-oracle result. The intermediate module fails
only after constructor allocation moves into Wasm and before setters do,
isolating the discrepancy to the mixed-runtime validation boundary.

## Semantic impact

The exhaustive Node checkpoint cone and the browser artifact gate cannot
validate staged helper internalization. This does not add an import to the
complete resident artifact, but it removes coverage of the transition that
the W6/W7 pipeline is intended to test.

## Classification and triage

Constructor headers carry the exact number of object slots, and Lean's
concrete ABI uses one machine-word representation for `object`, `tagged`, and
`tobject` slots. The missing information is validation provenance, not runtime
layout. The concrete host should reconstruct zero slots as erased/uninitialized
and populated unknown resident slots as `tobject`, then refine a slot when an
imported setter supplies its ABI kind.

## Workaround

The default Node gate skips intermediate pretty-format checkpoints unless
`FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1`; the browser gate does not skip them.
No workaround should be used for acceptance.

## Upstream tracking

none

## Resolution and regression

`ConcreteHost.constructorDescriptor` now reconstructs missing resident
allocation provenance from the concrete header's exact object-slot count and
physical words. It uses `erased` for zero slots and `tobject` for populated
unknown slots; an imported setter then refines the mutated slot to its declared
ABI kind. Mutation, recursive release, and observation all use this common
path.

`test-concrete-initial-runtime.mjs` removes the descriptor from a live
constructor before mutating it, directly exercising the resident-allocation
boundary. The exhaustive pretty-format checkpoint and browser artifact cone
retain the real staged-runtime regression.
