---
id: FIR-BUG-wasm-none-unreachable-fault-classification
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof-audit
first-seen: 2026-07-24
reproduction: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
regression: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
---

# Summary

FIR's explicit `RuntimeFault.unreachable` and the distinct
`RuntimeFault.invalidCases` fallback both lower to Wasm's native
`unreachable` instruction. Talos reports only the unstructured message
`"unreachable"` and leaves the concrete host failure channel empty.

## Minimal reproduction

Lower a supported nullary declaration whose body is
`.unreach LCNF.ImpureType.uint64`, adapt and resolve it, then execute its
export through the concrete Talos host.

The FIR interpreter returns `.fault .unreachable`. The generated target
returns `.Trap store "unreachable"` with `store.host.failure? = none`.

A constructor case without a matching constructor alternative or default has
the same target result, while FIR returns `.fault .invalidCases`.

## Exact commands

Run:

```text
make talos-check
```

The adjacent regression in `ConcreteRuntimeExamples.lean` checks both the FIR
fault and the empty concrete structured-failure channel.

## Expected semantics

Every source fault admitted by the Wasm fragment should retain enough
structured information at the target boundary to establish
`ConcreteErrorSourceRel` for that exact fault. In particular,
`unreachable` and `invalidCases` must remain distinguishable.

## Actual behavior

`Fir.Wasm.compileCode` maps an explicit `.unreach` to
`[.unreachable]`. `compileCaseFallbackWithM` uses the same instruction when a
case has no default. The adapter maps both to Talos `.unreachable`, whose
semantics is `.Trap store "unreachable"` and does not update
`Host.failure?`.

`RefinedFaultPost` requires
`final.host.failure? = some (.runtime failure.toTrap)`, so neither execution
can inhabit the public T4 endpoint.

## Proof or differential evidence

`Fir.Wasm.voidProgram` already demonstrates that explicit unreachability is
admitted by `supportedProgram`. The concrete regression demonstrates that the
target traps without a `ConcreteError`, while
`sourceCodeFault_execEvaluates` establishes the exact source observation.

## Semantic impact

T4 cannot cover every structured source failure admitted by
`WasmSupported`. The same unstructured target trap represents at least two
different FIR faults, so matching only the Talos message would lose source
operation and precedence information.

## Classification and triage

This is a lowering/runtime fault-transport gap. A clean repair should give
compiler-generated source traps a concrete structured payload, for example
through a dedicated runtime operation that W7 later internalizes. Merely
classifying every native Wasm `unreachable` as one FIR fault is insufficient.

## Workaround

Do not claim complete T4 coverage for explicit unreachability or missing case
fallbacks. Do not weaken `RefinedFaultPost` to accept an unstructured target
message.

## Upstream tracking

none

## Resolution and regression

unresolved
