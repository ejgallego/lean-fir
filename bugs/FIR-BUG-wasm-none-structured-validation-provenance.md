---
id: FIR-BUG-wasm-none-structured-validation-provenance
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-13
reproduction: integration/talos/FirTalos/ConcreteResumableWasm.lean
regression: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
---

# Summary

The structured simulation retained successful code adaptation for its current
LCNF node but not the source declaration and incremental validation state from
which `WasmSupported` accepted that node.

## Minimal reproduction

Attempt to construct `ConcreteStructuredCompilerCurrentStepAdmission.code`
from a `ConcreteSupportedFunction`, a current
`ConcreteStructuredCodeCoreRel`, and a successful source step. Adapter
inversion recovers generated instructions and numeric locals, but return,
join, case, and guarded sharing admission also need the source validator's
result kind, local-kind row, join points, case facts, and sharing facts.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteResumableWasm
```

Inspect `ConcreteSupportedFunction.validatedBody`,
`Fir.Wasm.supportedCodeWithJoins`, and
`ConcreteStructuredCompilerCurrentStepAdmission.code`.

## Expected semantics

Compiler admission should be derived from the actual declaration accepted by
`WasmSupported` and from a hereditary static validation invariant advanced in
lockstep with the existing dynamic structured relation. It should not be an
execution certificate supplied by the export theorem's caller.

## Actual behavior

Before the first repair slice, `ConcreteSupportedFunction` did not identify
its source declaration at all. The global relation also dropped the active
result equality before invoking compiler admission. Consequently the proof
could not connect a current adapted node to the exact validator judgment that
made it part of the compiler's supported domain.

## Proof or differential evidence

`CodeAdaptedWithSuffix.return_eq` supplies the compiled local kind but not the
source validator's result compatibility judgment. Similar gaps occur at joins
and guarded case/sharing paths where validation carries path-sensitive facts.
The residual-state proof also exposed that `supportedCodeWithJoins` was an
opaque `partial def`, so Lean provided no equations with which to invert even
an available validator hypothesis.

## Semantic impact

Without this provenance, a universal admission theorem would either remain
unprovable or require a new caller-supplied recursive certificate, contrary to
the intended self-verified compiler theorem.

## Classification and triage

This is a proof-relation invariant omission. It does not change source
semantics, the symbolic Wasm ABI, the concrete runtime, or generated code.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. `ConcreteStructuredValidationFocus` now supplies the root and
proof-visible residual transition laws. Resolution requires attaching that
state to active and suspended structured relations and deriving universal
current-node admission from it.

## Progress

The first repair slice makes every `ConcreteSupportedFunction` retain its
exact source declaration, body identity, declaration lookup, and effective
result ABI. `ConcreteSupportedFunction.validatedBodyAt` now reconstructs the
real root `supportedCode` judgment at the active result kind, and the compiler
admission law receives the existing active-result equality.

The second repair slice replaces the opaque validator with a terminating
syntax traversal and proves that its alternative-list traversal is
extensionally the former `Array.all` check. The new
`ConcreteStructuredValidationFocus` stores the exact residual Boolean
judgment, reconstructs its root from `validatedBodyAt`, and has checked
inversion/continuation laws for `let`, join/jump, cases and selected
alternatives, ownership, deletion, tag mutation, and every field-mutation
form. The remaining work is to attach that focus to the structured code/frame
relation and derive each current-node admission constructor from it plus the
successful source step. Return admission has a separate compatibility
overstrengthening recorded by
`FIR-BUG-wasm-none-return-admission-refinement-direction`.

The residual focus and suspended validation are now attached throughout the
closed structured relation, including direct and saturated calls, returns,
lazy-cache publication, external bind resumption, cases, ownership, and field
mutation. The first admission inversion identifies the remaining static
bridge precisely: the path-sensitive validator local row must agree, on every
successful lookup, with the production compiler context. Under that agreement,
ordinary decrement admission follows from the validator and successful source
step alone. Ordinary increment has the same compiler derivation but exposes an
independent finite-header headroom condition recorded by
`FIR-BUG-wasm-none-finite-trace-refcount-overflow`.

The production-root bridge is now closed. `ConcreteSupportedFunction` retains
the generated function/declaration name identity, from which the successful
lowering table and compiler-derived name uniqueness recover the exact
`LoweredInternalDeclaration`. The validator and lowerer are proved to compute
the same parameter row; name-directed lookup is invariant under reversal of
that duplicate-free row and remains valid when body locals are appended.
Consequently `ConcreteSupportedFunction.rootAlignedValidationState` constructs
root validation together with production-local agreement without a
caller-supplied certificate. The remaining provenance work is hereditary:
preserve aligned validation through residual code/frame transitions and use it
in the universal current-step admission theorem.

The first hereditary slice packages ordinary increment and decrement admission
over the aligned residual invariant and carries that invariant through their
continuations unchanged. A direct `let` continuation now extends agreement with
the exact result binding chosen by both the validator and production compiler.
The remaining `let` obligation is therefore syntax-local: derive that compiled
binding from the operation-specific adaptation theorem. Join, case, call-entry,
and suspended-frame transport remain to be connected before the universal
current-step admission theorem can replace per-constructor hypotheses.

Explicit deletion is now classified from the aligned validator state and the
actual successful source step alone, and alignment is preserved across delete,
tag, object-field, `USize`-field, and packed-scalar-field continuations. While
closing the direct-`let` result premise, the proof exposed that raw supported
lowering does not retain body-binder name uniqueness; that independent domain
defect is recorded as `FIR-BUG-wasm-none-local-binder-name-uniqueness`.

Persistent increment and decrement are now complete validator-derived
admission cases: their source-visible nodes are erased by production lowering
and require no target or heap premise. The mutation audit also confirmed that
set-tag validation lacks the `UInt32` range premise required by the concrete
header theorem; `FIR-BUG-wasm-none-settag-uint32-admission` records that
independent compiler-domain gap. Return admission remains deliberately
directional until upstream typing/value-shape information can justify the
reverse object-family orientations accepted by physical compatibility.
