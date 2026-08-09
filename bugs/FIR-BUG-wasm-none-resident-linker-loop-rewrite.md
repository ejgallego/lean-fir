---
id: FIR-BUG-wasm-none-resident-linker-loop-rewrite
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-09
reproduction: Fir/Wasm/Emit/ResidentClosureAllocation.lean
regression: Fir/Wasm/Emit/ResidentClosureAllocation.lean
---

# Summary

Resident partial-application internalization does not rewrite runtime calls
nested inside a symbolic Wasm loop, and repeatedly traverses the whole module
once for every helper operation.

## Minimal reproduction

Compile the final-LCNF closure of
`VersoSlides.Pretty.formatRenderedForRuntime`. Its closure allocation and
projection families contain many distinct runtime operations across a large
module. The existing partial-application rewrite descends through blocks and
conditionals but omits `.loop`; the other helper families internalize each
operation with another complete module traversal.

## Exact commands

Run the Flat integration compiler after preparing its pinned Verso source
view:

```sh
cd integration/verso-flat
./check.sh
```

## Expected semantics

Every selected runtime call should be replaced at any structured-control
depth. A complete helper family should be installed with one deterministic
whole-module rewrite while preserving the exact runtime-operation order.

## Actual behavior

A selected partial-application call under `.loop` remains unresolved. Large
closures also spend most of their linking time repeatedly walking already
rewritten functions.

## Proof or differential evidence

The closed Flat artifact cannot satisfy the zero-import postcondition unless
all reachable calls are rewritten. The final external-engine differential
suite checks the exact native result, so a wrongly selected or missed helper
cannot be hidden by a host fallback.

## Semantic impact

Compiler-generated loops can leave a resident runtime import in an otherwise
self-contained module. Repeated traversal additionally makes publication of
larger source closures unnecessarily slow.

## Classification and triage

This is a Wasm resident-linker implementation gap. It does not change the
symbolic instruction surface, concrete layout, runtime operation signatures,
or W6 proof contracts.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The read-projection, closure-projection, closure-match, scalar-box, and
partial-application families now collect physical bindings first and rewrite
the module once per family, recursively including loops. The Flat source
closure is the permanent multi-operation regression; its package gate requires
zero imports and zero residual runtime operations before external execution.
