# W6 fault and target-safety audit

This document separates two obligations that were previously grouped under
“structured faults.” They have different statements and must not be proved by
weakening one relation to cover the other.

## A. Source-fault preservation (T4)

T4 applies when FIR reaches a `RuntimeFault`. The generated target must trap
with a source-classified `ConcreteError` related to that exact fault:

```lean
ExecEvaluates sourceExternals initialSource
  (FaultObservation faultRuntime fault)
∧
ConcreteExportTrapsWith hostEnv module exportName arguments
  (RefinedFaultPost faultRuntime fault)
```

`ConcreteErrorSourceRel` deliberately accepts only `.source` and
`.sourceAddress`. It does not accept malformed target memory, ABI-shape
errors, native Wasm traps, or concrete-global failures.

`ConcreteFaultSimulation` transports a terminal fault through every
successfully simulated source/target prefix. The arbitrary-arity
`concreteFaultLeaf_external_sourceFailure` now closes the foreign-call
boundary: after argument decoding, the same external source fault is retained
through the generated local-load/call/local-set sequence.

## B. Target safety (T4S)

A target-only failure says that the concrete representation, generated ABI,
or finite wasm32 resource model failed where FIR has no corresponding
`RuntimeFault`. Such a failure cannot satisfy T4. The required theorem shape
is instead:

```lean
related initial concrete/source state
→ admitted operation or code step
→ concrete execution does not produce a target-classified failure
```

Allocation requires an explicit resource premise: FIR's semantic heap is
unbounded, while wasm32 has a finite address space. In-place reuse additionally
requires a retained-capacity invariant. These premises must come from the
validated fragment or the public theorem; they may not be smuggled into an
operation equation supplied by the caller.

Malformed concrete headers, noncanonical padding, missing closure metadata,
and invalid generated globals are likewise T4S obligations. A
`ConcreteRuntimeRel` or resolver invariant should make them impossible. If it
does not, the discrepancy needs a bug card or a stricter fragment gate.

## Audited source-fault matrix

“Leaf” means a terminal `ConcreteFaultLeaf` can be built from the current
runtime refinement theorem. “Exact runtime” means the concrete operation
already emits the same `.source` fault, but its generated terminal leaf or
the premise that derives its operation equation remains to be packaged.

| Family | FIR failures after successful operand lookup | Status |
|---|---|---|
| literals | none | T4 not applicable; allocation resource failures are T4S |
| constructor allocation | malformed field arity | statically excluded by `WasmSupported`; concrete classification mismatch is `FIR-BUG-wasm-none-constructor-arity-fault-classification` |
| object projection | `expectedConstructor`, `deadObject`, `objectFieldOutOfBounds` | all three exact terminal leaves complete |
| `USize` projection | `expectedConstructor`, `deadObject`, `usizeFieldOutOfBounds` | all three exact terminal leaves complete |
| packed-scalar projection | `expectedConstructor`, `deadObject`, `scalarFieldMissing` | constructor/dead leaves complete; missing-coordinate mismatch is `FIR-BUG-wasm-none-uninitialized-scalar-projection` |
| constructor cases / `getTag` | `expectedConstructor`, `deadObject`, `invalidCases` | constructor/dead leaves complete; missing-alt fallback is blocked by `FIR-BUG-wasm-none-unreachable-fault-classification` |
| object and `USize` mutation | `expectedConstructor`, `deadObject`, bounds | all exact terminal leaves complete |
| packed-scalar mutation and tag mutation | `expectedConstructor`, `deadObject` | all exact terminal leaves complete for every supported integer width |
| `isShared` | `expectedObject`, `deadObject` | dead leaf complete; the ABI relation excludes `expectedObject` for an admitted related operand |
| increment / decrement / delete | `expectedObject`, `expectedHeapReference`, `deadObject`, `referenceCountUnderflow`, recursive child faults, release-fuel `malformed` | mapped stale, direct underflow, arbitrary-depth recursive decrement, and unchecked tagged increment/positive-decrement leaves complete; ABI relations exclude the other operand-shape cases; the semantic public budget and concrete mapped host both exclude release-fuel exhaustion |
| box | `expectedScalar` | admitted scalar relations exclude it; allocation resource failures are T4S |
| unbox | `expectedObject`, `expectedScalar`, `deadObject`, unknown scalar type `malformed` | `expectedScalar` and `deadObject` exact terminal leaves complete; the admitted `.tobject` relation excludes `expectedObject`, and supported boxed kinds exclude unknown-type faults |
| reset | `expectedObject`, `deadObject`, `expectedConstructor`, object bounds, decrement/child faults | dead-object, unique-nonconstructor, unique-constructor bounds, nonunique fallback decrement, and non-`expectedObject` unique-constructor child-fault leaves complete; `.tobject` excludes operand-shape `expectedObject`; every mapped branch excludes release-fuel target traps, while erased child source release is tracked by `FIR-BUG-wasm-none-reset-erased-child-release` |
| reuse | `expectedReuseToken`, malformed arity, `deadObject`, `expectedConstructor` | dead-object and live-nonconstructor terminal leaves complete; admitted token/static-arity gates exclude the first two; the wasm32 capacity analysis supplies fitting evidence, its dynamic value relation ties retained evidence to the exact live header, and the in-place operation theorem now derives rather than assumes the retained-layout inequality required by T4S |
| partial application | unknown declaration and saturated/malformed partial application | excluded by the supported static call gate; allocation and metadata failures are T4S |
| closure application | `expectedClosure`, `deadObject`, declaration/arity faults | closure-flow gate excludes declaration/arity and untracked closure shapes; expected-closure/dead terminal packaging and closure-metadata T4S remain |
| exact external call | arbitrary `RuntimeFault` returned by the installed implementation | arbitrary-arity terminal leaf complete |
| explicit `.unreach` | `unreachable` | blocked by `FIR-BUG-wasm-none-unreachable-fault-classification` |

Lookup/control failures (`unknownVar`, `unknownDecl`, `unknownJoinPoint`, and
call/join arity mismatches) are intended to be excluded by validation and
reachable-state invariants. The remaining completeness task is to connect the
boolean `WasmSupported` evidence to those invariants rather than adding target
traps for malformed source code.

## Confirmed gaps

- `FIR-BUG-wasm-none-unreachable-fault-classification`: explicit
  unreachability and a missing case alternative both become the same native
  Wasm trap with an empty structured-failure channel.
- `FIR-BUG-wasm-none-uninitialized-scalar-projection`: FIR faults on an
  unwritten packed coordinate while zero-filled concrete storage returns zero.
- `FIR-BUG-wasm-none-constructor-arity-fault-classification`: the two runtimes
  choose different fault constructors for malformed allocation arity; valid
  admitted calls are statically aligned.
- `FIR-BUG-wasm-none-reset-erased-child-release`: erased is an admitted
  constructor ownership slot, but FIR reset's `decValueOnce` faults while
  concrete checked decrement skips the physical zero sentinel.

## Next proof slices

1. Resolve the structured `unreachable` transport as an isolated semantic
   Wasm ABI change, then rebase both tracks.
2. Preserve `ReuseCapacityValueRel` through constructor, reset, and reuse
   steps, then carry it through the syntax-directed simulation. The operation
   boundary already derives layout fit from the static and dynamic evidence.
3. State and prove T4S per operation, including explicit wasm32 allocation
   capacity, then compose it syntax-directly alongside T2/T4.
