---
id: FIR-BUG-wasm-none-resident-client-frontier-publication
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: a669b51d86af72a7de5634b458ccd0f33755ae3b
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-29
reproduction: integration/talos/artifact/resident-big-numeric-client.mjs
regression: integration/talos/artifact/resident-big-numeric-client.mjs
---

# Summary

The resident numeric Node client published the host heap frontier before raw
input allocation but not afterward, allowing the next Wasm allocation to
overwrite the final input object.

## Minimal reproduction

Allocate a negative five-limb Integer through `ConcreteHost.allocateInteger`,
then call the resident `Int.natAbs` helper without publishing the updated host
cursor. The helper allocates its result at the input address and destroys the
source before copying all limbs.

## Exact commands

From `integration/talos/artifact` after emitting the standalone artifact:

```sh
lake exe fir-wasm-artifact resident-big-numeric \
  _build/resident-big-numeric.wasm
node run-resident-big-numeric.mjs _build/resident-big-numeric.wasm
```

## Expected semantics

The host publishes every raw heap allocation before entering a resident Wasm
export. Resident allocation must therefore start after all input objects, and
`Int.natAbs (-a)` must return `a` for an arbitrary-precision magnitude.

## Actual behavior

The first failing run returned only the low word `1985229329`. Inspection
showed both input and output at address `1024`: the result header replaced the
input header before the recursive copy read its payload.

## Proof or differential evidence

All preceding 256–384-bit Natural arithmetic and comparison checks passed.
The exact `Int.natAbs` assertion failed, and the physical header dump showed
the aliasing address and the overwritten Natural result header.

## Semantic impact

This affected low-level JavaScript consumers that allocate the last argument
directly in module memory and then invoke an allocation-producing resident
export. The Wasm helper and W6 layout were not at fault.

## Classification and triage

This is a host-facade frontier-protocol bug. `resident-string-client.mjs`
already implements the required post-allocation publication sequence.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Both resident numeric clients now synchronize the shared frontier immediately
after each raw Natural/Integer input allocation. The arbitrary-precision
client permanently exercises a copying operation whose source must survive
the result allocation.
