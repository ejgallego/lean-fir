# W6/W7 theorem roadmap

This document states the proof obligations for the concrete WebAssembly lane.
The operation inventory in `W6-COVERAGE.md` records which local runtime rules
exist; this roadmap records the program theorems those rules must build.

The boundaries here are intentionally allowed to evolve. Clients may
experiment against them, but should expect to adapt when a cleaner statement
or representation makes a proof substantially better.

## Semantic endpoints

The first pragmatic endpoint is conditional preservation of a finite source
behavior. It does not prove that any source program terminates:

```lean
ExecEvaluates sourceExternals
  (sourceCodeState context sourceRuntime sourceEnv sourceCode)
  (ReturnedObservation resultRuntime resultValue)

→ ∃ resultKind,
    ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
      initial arguments
      (RefinedReturnPost resultRuntime resultValue resultKind callerTail)
```

Talos's `TerminatesWith` is used only in the consequent, after a finite source
evaluation has been supplied. This is compiler partial correctness, not a
source termination theorem. The first return slice consumes the existing
source `CodeEvaluates` derivation and derives its canonical `ExecEvaluates`
run; subsequent slices move the compiler theorem directly over the canonical
machine evaluation.

`RefinedReturnPost` must state all of the following:

1. the concrete run returns exactly one physical value and preserves the
   caller operand tail;
2. the final concrete runtime refines `resultRuntime` under some
   `RefinementWitness`;
3. the structured concrete failure channel is clear; and
4. the physical result refines `resultValue` at `resultKind`.

`ConcreteRuntimeRel` already includes heap, globals, world, and trace. The
public success theorem therefore does not need a second observation relation
that could silently omit part of the runtime.

## The theorem ladder

### T1. Verified static pipeline

`ConcreteSupportedExport` is the static compiler boundary. It records
successful admission, lowering, adaptation, concrete-host resolution, and
export lookup. It now also records two facts that must be derived from the
compiler rather than supplied by a dynamic simulation object:

- `bodyAdapted`: the selected source code passes through the actual
  `compileCode` and numeric adapter to the selected target function body; and
- `localsAligned`: the lowering context and selected symbolic function assign
  the same ABI kind and numeric slot to every compiled local read; and
- `runtimeCallsAligned`: each symbolic runtime call selected by the adapter
  has the same numeric target import, concrete resolved-host contract, and
  parameter/result arity.

These fields are temporary explicit invariants until the corresponding
`lowerDecl`/whole-module theorems construct them automatically. They contain
no source execution or target execution evidence.

### T2. Direct partial compiler correctness

The main W6 theorem is a function from a source evaluation to matching target
execution. It is proved structurally from the executable compiler, with cases
for:

- return;
- direct value `let`;
- object and scalar cases;
- no-result effects;
- direct and closure calls;
- external calls; and
- lazy-cache hit and miss paths.

At each node the proof inverts the actual compiler equation, applies the
operation refinement theorem, establishes the generated local/control
plumbing, and recurses on the source evaluation. The intended public shape is:

```lean
compileCode context sourceCode = .ok symbolicTarget →
instructions sourceModule sourceFunction [] symbolicTarget = .ok targetBody →
StateRelated ... →
ExecEvaluates sourceExternals sourceState observation →
TargetBehaviorRel observation targetBody
```

`CodeWP`, `SuccessfulDeclaration`, `ConcreteCodeSimulation`, and
`ReuseCapacityCodeSimulation` remain internal compatibility lemmas while
their operation results are migrated. They are not premises of the final
compiler theorem.

`ConcreteSupportedExport.correctReturn` is the first completed T2 case. It
derives the emitted return body, ABI kind, numeric local, exact target return,
and source execution from the static pipeline and source return evaluation.
`ConcreteSupportedExport.correctNaturalLiteralReturn` is the first
compositional case: it derives the exact
`call; local.set; local.get; return` body and resolved natural-literal
contract, executes concrete allocation, extends the heap witness, and proves
the source and exported target return the related result. Its only dynamic
side conditions are allocation success and capacity for the checked local
write.
`CodeAdapted.let_eq` now supplies the reusable inverse compiler/adaptor rule
for every direct `let`: successful whole-body compilation is split into the
separately compiled and adapted value and continuation plus the numeric
destination local. `naturalLiteralLet_eq` specializes that rule, and
`ConcreteSupportedExport.codeWP_naturalLiteralLet` composes the concrete
literal step with an arbitrary compiler-selected continuation. Its recursive
premise is the semantic correctness induction hypothesis for that
continuation, not a caller-built translation certificate.
`stringLiteralLet_eq` and `codeWP_stringLiteralLet` provide the equivalent
recursive rule for exact UTF-8 String allocation in the `.object` lane.
`correctStringLiteralReturn` also closes the finite whole-export String
instance through the concrete resolver contract and heap-witness extension.
Both String rules now use the source-facing
`MemoryState.AllocationCapacity`, not a concrete-success equation:
`AddressSpaceBudget` plus the related frontier constructs raw allocation,
header installation, and the full UTF-8 payload write. The exact budget
consumption theorem is the resource transport intended for allocating
direct-value induction. `codeWP_stringLiteralLet_of_budget` now consumes that
transport and supplies the exact residual budget to an arbitrary
compiler-selected continuation. The indexed
`codeWP_of_directValueEvaluates_withCost` structural theorem now automates
that composition for arbitrary finite String-literal spines from one
source-computed `DirectValuePathCost`. The nonempty-constructor runtime
instance now derives mixed arguments and exact residual layout cost, so
arbitrary finite constructor spines use the same theorem. Mixed read-only
composition now includes cost-zero local aliases and immediate integer/`USize`
literals plus successful object, `USize`, and packed-integer scalar projections
through `BudgetedDirectSupported`. The projection instances preserve the
concrete heap exactly and return the full residual address-space budget.
Natural literals now use the same indexed law. `naturalAllocationBytes`
classifies their concrete cost as zero for wasm32-tagged immediates, an
aligned one-slot object for promoted source tags, or an aligned limb object
for arbitrary-precision values. `allocateNatural_eq_ok_of_budget` constructs
all three cases from the frontier invariant and one source budget and exposes
the exact residual headroom. Thus `NaturalLiteralSupported` admits arbitrary
Nat-literal and mixed spines without a concrete allocation-success premise or
target representation witness; this proof-facing classifier remains an
unstable implementation boundary.
`ConcreteSupportedExport.correctBudgetedDirect` now turns the resulting
structural `CodeWP` into the public named-export statement: finite source
evaluation plus one source-path budget implies the matching source observation
and fuel-free concrete Wasm termination under `RefinedReturnPost`.
`ConstructorArgsCompiled` is a syntax-directed characterization proved from
the production `compileArgs` fold. Combined with successful source evaluation,
real Talos adaptation, `LocalLayoutAligned`, and `StateRelated`,
`constructorArgsReady_of_compileArgs` derives the exact physical prefix:
numeric local reads for ordinary fields and canonical zero constants for
erased fields. `constructorLet_eq` recovers the import, destination, and
continuation; `codeWP_constructorLet` composes an arbitrary continuation; and
`correctConstructorReturn` closes the finite export. The earlier all-local
rules remain compatibility corollaries, not the public proof boundary.
`ConcreteCompilerCorrectnessContract.lean` is a compile-time harness ensuring
that the finite return/Nat/String/constructor export theorems and the
literal/constructor recursive rules have no translation-certificate premise.

### T3. Whole-export success

Combining T1 with the direct T2 theorem must yield:

```lean
ExecEvaluates ... observation →
∃ resultKind,
  ConcreteExportTerminatesWith ... (RefinedReturnPost ...)
```

This theorem must use the exported function selected from the generated
module, not a hand-written body or fixture-specific index, and must not accept
a caller-built simulation derivation.

### T3S. Finite traces and weak simulation

After the finite-return theorem covers the supported compiler, introduce a
relational target execution layer adequate to Talos `exec`/`run`. The next
endpoint is finite-prefix preservation and then weak simulation; backward
matching may be added to obtain weak bisimulation. This layer captures
divergence without adding termination assumptions to compiler correctness.
The state relation and operation lemmas used by T2 must therefore remain
independent of Talos's total-correctness `wp`.

### T4. Structured faults

Fault correctness is a separate theorem, not a disjunct hidden inside T1:

```lean
source reaches sourceError
→ concrete target terminates in the corresponding structured failure
```

The relation is `ConcreteErrorSourceRel`. The proof must retain operation and
precedence information for source faults, including stale-object, bounds,
source-classified malformed requests, and external failures. A target trap
without the related structured source error does not satisfy this theorem.
Typed unboxing now supplies both reachable terminal instances: stale mapped
objects preserve their related physical/source address in `deadObject`, while
live represented non-box objects preserve `expectedScalar`. The admitted
`.tobject` and `BoxedScalarKind` gates exclude its other source fault forms.
Reset likewise supplies exact terminal instances for stale mapped objects and
for live, nonpersistent, uniquely owned nonconstructors. Those ownership
premises are part of the theorem boundary because shared or persistent cells
take reset's decrement fallback before the constructor-kind check.
Nonempty reuse supplies exact terminal instances for stale mapped tokens and
live mapped nonconstructors after the aligned field-arity gate. The admitted
reuse-token relation and compiler-selected arity exclude its earlier token
shape and malformed-arity faults; retained allocation capacity remains a
separate target-totality obligation.
Reset's remaining pre-release branch is also exact: a live, nonpersistent,
uniquely owned constructor with `objectFields.size < count` preserves the
complete `objectFieldOutOfBounds count size` payload and traps before clearing
fields or decrementing children.
Direct ownership underflow is exact as well: every represented mapped live,
nonpersistent cell with reference count zero exposes a matching non-promoted
physical header, and any positive decrement preserves
`referenceCountUnderflow` at the related word/location. The generated unary
call traps before a header write, ownership-metadata read, recursive child
release, or continuation. Faults reached after a count-one parent has been
released remain the separate recursive-child obligation.
The ordered ownership-fold core now handles that obligation's inner loop:
successful earlier child releases advance both related heaps, the first
failing child retains its exact `ConcreteErrorSourceRel`, and later children
are unreachable. Constructor/closure parent-release and generated terminal
packaging remain to connect this reusable fold theorem to T4.
Mapped-heap decrement now completes that connection. A same-fuel induction
handles stale cells, direct underflow, constructor and closure parent release,
and arbitrary recursive children. A separate non-fuel error monotonicity
theorem lifts the result to the larger cursor-derived concrete budget, and a
repetition induction preserves the first fault after successful earlier
decrements. The Talos and compiler/adaptor leaf retain exact
`ConcreteErrorSourceRel` with explicit closure-descriptor identity. The
following slices discharge unchecked tagged operands, reset's child-release
wrappers, and public release-fuel target safety separately.
The tagged obligation is now closed: unchecked increment faults immediately,
and every positive unchecked decrement faults on its first repetition, for
both immediate and promoted physical tag representations. Their Talos and
compiler/adaptor leaves preserve exact `expectedHeapReference` and make the
continuation unreachable. Zero decrement remains the intentional empty fold.
Unique-constructor reset now reuses the public recursive decrement boundary:
the cleared-prefix ownership relation advances through successful children,
the first mapped child fault retains its exact address/location relation, and
the pure reset/host computations discard the intermediate protocol heap on
error. The Talos and compiler/adaptor leaves therefore trap from the original
related store before writing the reuse-token local. The theorem excludes
`expectedObject` because erased is an admitted ownership slot but FIR reset
currently faults where concrete checked decrement skips physical zero; this
shared-contract discrepancy is tracked by
`FIR-BUG-wasm-none-reset-erased-child-release`. Reset's nonunique fallback
decrement is now packaged separately: any non-fuel fault from that delegated
public checked decrement crosses the reset host and compiler terminal leaf
unchanged, before the empty token local or continuation.
Release-fuel target safety is now closed for mapped ownership operations.
A live-cell measure proves FIR's public budget cannot return its internal
fuel marker; success/fault refinement excludes the concrete target error for
one decrement and every repetition. The ownership-list lift includes erased
slots, and the complete reset theorem covers dead, fallback, kind, bounds,
and in-bounds unique-prefix branches. Talos decrement and reset host calls
therefore cannot emit the structured release-fuel target trap.

The public endpoint is now explicit:

```lean
ExecEvaluates sourceExternals
  (sourceCodeState context sourceRuntime sourceEnv sourceCode)
  (FaultObservation faultRuntime fault)
∧
ConcreteExportTrapsWith hostEnv module exportName arguments
  (RefinedFaultPost faultRuntime fault)
```

`RefinedFaultPost` requires both `ConcreteRuntimeRel` at the source fault
runtime and a `HostFailure.runtime` whose underlying `ConcreteError` satisfies
`ConcreteErrorSourceRel` for `fault`. `ConcreteTrapsWith` supplies the
fuel-independent target endpoint missing from Talos's success-only
`TerminatesWith`, and the body-WP/export bridges are complete.
`ConcreteFaultSimulation` now constructs both halves by transporting a
terminal failing leaf through every successful prefix constructor from T2.
The remaining obligation is the operation-level leaf matrix: each admitted
source failure must construct `ConcreteFaultLeaf` without losing its exact
payload or precedence. Projection, mutation, ownership, tag, case-tag, and
arbitrary-arity external terminal leaves are present. Direct object, `USize`,
and packed-scalar projection plus mutation now preserve the common
`expectedConstructor` gateway across every admitted related operand; tag
mutation and object-mode case discrimination share the same boundary. The
exact matrix and known blockers are maintained in `W6-FAULT-AUDIT.md`.

### T4S. Target safety

Malformed concrete layout, ABI-shape errors, allocation exhaustion, missing
generated metadata, and concrete-global failures are not FIR runtime faults.
They therefore cannot be folded into `ConcreteErrorSourceRel`. W6 also needs
the separate safety statement that these target-classified traps are
unreachable from a related state under the validated fragment and explicit
wasm32 resource premises.

Allocation capacity and retained reuse capacity must be visible hypotheses or
validated invariants. FIR's semantic heap is unbounded, so unconditional
target totality would be false. `reuseCapacitySafeProgram` now rejects unknown
token provenance and records fitting evidence for every admitted nonempty
reuse. `ReuseCapacityValueRel` gives that evidence a dynamic interpretation at
the exact physical heap header, and `reuseStep_some_of_capacityEvidence`
derives the operation theorem's retained-layout premise from the two. The
whole static map is now interpreted by `ReuseCapacityFactsRel` inside
`ReuseCapacityStateRelated`; its generic transport/bind rule reduces syntax
preservation to proving `HeaderCapacityTransport` for each successful
operation family. That boundary is scoped to witness-related, frontier-owned
headers rather than arbitrary readable memory. Prefix-extension proofs
instantiate it for nonempty constructor allocation and nonempty reuse from the
zero token, while a unique-reset bridge changes retained object evidence into
same-address token evidence. The in-place reuse byte transaction now preserves
the target's allocation word, frames all other mapped allocations through
descriptor disjointness, and exports that transport through both the concrete
and Talos operation theorems. Unique reset now composes bounded prefix writes
with recursive ownership-release transport and carries the retained object
bound to the returned token. Empty constructors now cover both immediate
tagged identity transitions and fresh promoted-tag prefix extensions through
the same transport boundary. Ownership operations now expose transport for
increment, recursive decrement, and deletion. Mutation operations expose it
for constructor tags, object fields, `USize` fields, and every supported packed
integer width. The operation-level transport inventory is complete; the
complete no-result effect spine now carries it through generic effect-step and
heap-replacement adapters, with reflexive transport for persistent ownership
effects. Generic result-binding rules now insert tracked evidence or erase a
shadowed stale fact across the checked local write and the same transport
boundary. Constructor, reset, and reuse supply their exact validator-selected
result evidence in every successful physical branch; nonunique and unique
reset also preserve unrelated mapped-header facts. The direct-let transfer
surface now has named constructor/reset/reuse adapters plus two exhaustive
ordinary-result shapes: heap preservation for reads and fresh-prefix
extension for allocation. Boxing, natural, string, and partial-application
allocation instantiate the latter across all admitted representations. The
authoritative let-fact transfer has been extracted from the validator, and
`ReuseCapacityCodeSimulation` now states the recursive certificate across
direct lets, calls, externals, lazy-cache paths, cases, and effects. It exposes
initial and selected-return fact interpretations and erases to the existing
executable simulation and `CodeWP`. The remaining syntax work is to construct
that certificate from each operation theorem, with the interprocedural call
transition the main open composition boundary. Native
unreachability losing its source fault is tracked separately by
`FIR-BUG-wasm-none-unreachable-fault-classification`.

### T5. Wasm-resident runtime linking

W7 replaces concrete host functions with Wasm-resident implementations over
`WebAssembly.Memory`. For each currently concrete-resolved `RuntimeOp`, prove:

```lean
internalRuntimeFunction implements concreteHostFunction
```

The linking theorem then replaces calls to concrete runtime imports by calls
to those internal functions while preserving T3's result. This theorem is the
proof boundary between W6's concrete-runtime semantics and W7's generated
self-contained artifact.

JavaScript implementations remain useful executable oracles, but are not the
implementation quantified over by T5.

### T6. Import closure

After linking, inspect the final module and prove that every remaining function
import corresponds to a genuine source external. Consequently, a pure source
program has no function imports:

```lean
source program has no externals
→ linkedModule.functionImports = []
```

For the pure `prettyM` target, the artifact acceptance criterion is:

- zero function imports;
- exported linear memory and the agreed low-level construction operations;
- agreement with the existing Node, Chrome, and native-oracle tests; and
- the T3 result transported through T5.

## Completion criteria

W6 program correctness is complete when:

- T1 is implemented and used as the common declaration boundary;
- T2 covers every operation admitted by the supported fragment;
- T3 is proved without fixture-specific compiler or layout assumptions;
- T4 covers every structured failure admitted by that same fragment; and
- T4S excludes target-only traps under the stated representation and resource
  invariants; and
- direct recompilation, `make check`, and `make talos-check` are green.

W7 self-containment is complete when T5 covers every concrete runtime import
used by the target, T6 establishes the import claim, and the external-engine
acceptance tests pass.

## Work order

1. In progress: prove T1 directly from `lowerDecl`, `lowerSupported`, `adapt`,
   and `resolveHosts`; the explicit `bodyAdapted`, `localsAligned`, and
   `runtimeCallsAligned` fields are the current theorem targets, not client
   obligations to preserve indefinitely.
2. Completed base case: derive return compilation/adaptation and exported
   target execution from a source return evaluation. Keep the
   certificate-free application in
   `ConcreteCompilerCorrectnessContract.lean`.
3. Completed direct-value instances: natural and UTF-8 String literals,
   mixed local/erased constructor allocation, and object/`USize`/packed-scalar
   projections now use the actual compiler/adaptor
   equations, resolver alignment, concrete allocation refinement, checked
   local writes, and arbitrary continuations. Literal and constructor families
   also have finite return corollaries. The first structural direct-`let`
   theorem now covers arbitrary finite return/direct-value spines. Its
   `DirectLetRuntimeRefines` premise is a uniform runtime law over
   compiler/adaptor outputs, parameterized by the admitted declaration
   predicate and the resource invariant; it is not a per-program translation
   certificate. The zero-argument local-alias instance is constructive:
   `ConcreteLocalFrameAligned` makes compiler-resolved destination writes
   total and is preserved by `local.set`; the contract harness composes two
   such declarations. Successful object and `USize` source projections now
   recover constructor-descriptor existence from `ConcreteRuntimeRel`;
   object projection retains only selected-field ABI-kind agreement and
   `USize` projection retains no heap-shape premise. The constructive runtime
   law now covers arbitrary admitted `USize`-projection spines: compiler and
   adapter inversion, related physical object resolution, automatic descriptor
   recovery, resolved host execution, and total i64 local writes discharge the
   uniform step interface. Object projection now discharges the same interface
   from its one selected-field ABI-kind typing obligation; the compiler,
   adapter, heap relation, concrete read, and local write supply everything
   else. `ReadOnlyDirectSupported` composes aliases and both projection
   families into mixed spines. Packed-scalar projections and nonallocating
   literals now join that structural fragment. UTF-8 String and nonempty
   constructor allocation have constructive wasm32-capacity boundaries.
   Compiled constructor arguments now derive their mixed local/erased physical
   relation, exact i32 decoding, and pointwise source refinement, and both the
   recursive and finite nonempty-constructor theorems consume that boundary
   without an opaque concrete step. Exact residual budgets are now exposed by
   object, String, and nonempty-constructor allocation; the String recursive
   compiler theorem passes its remainder to the continuation. The structural
   runtime law now has before/after resource indices and an arbitrary finite
   String-spine instance. Nonempty constructors now have the corresponding
   indexed runtime law and arbitrary-spine contract. Cost-zero local aliases
   and immediate literals now compose with both allocating families in one
   arbitrary-spine contract. Lift successful projections into that indexed
   union next.
4. Extend the direct theorem across cases, effects, calls, externals, and lazy
   caches. Reuse the existing W6 operation lemmas, but do not expose
   `ConcreteCodeSimulation` or `ReuseCapacityCodeSimulation` as premises.
5. Lift from the current source evaluation view to canonical
   `ExecEvaluates`, then package the complete generated export as T3.
6. Migrate T4 and T4S to consequences of the same structural compiler proof.
   Retained reuse capacity is validated and its
   static-to-concrete operation bridge and whole-fact-map invariant are proved;
   fresh nonempty allocation and zero-token reuse supply header-capacity
   transport, in-place reuse carries mapped-header transport through the
   validator-backed operation theorem, and unique reset carries the same
   transport through prefix clearing and recursive child release. Empty
   constructor allocation/reuse covers immediate and promoted tagged results;
   ownership and mutation operations now supply transport across every
   admitted successful effect. The complete no-result effect spine carries the
   strengthened state through generic effect-step adapters. Result bindings
   now have generic insert/erase adapters, and constructor/reset/reuse supply
   their exact tracked evidence plus old-fact transport. All current direct
   result families reduce to named tracked transfer, heap-preserving erasure,
   or prefix-extending erasure. The existing recursive capacity-aware
   derivation remains a source of reusable transport lemmas while its facts
   move into the direct compiler state relation. Result steps now have one
   common capacity-preserving
   contract with named direct, external, lazy, and call instantiations. The
   call specialization identifies the remaining callee obligation exactly:
   the ordinary call simulation plus its destination-local update, witness
   transport, and retained-header transport. The remaining syntax work is to
   consume these contracts in the direct operation and callee cases.
   Structured unreachability remains the shared-contract blocker.
7. Add a target relational execution/adequacy layer and prove finite-prefix
   preservation, divergence preservation, and then weak simulation or weak
   bisimulation as useful.
8. Let W7 generation proceed independently against the current concrete
   runtime surface, then prove T5 per internalized runtime function.
9. Close with T6 and the pure `prettyM` acceptance theorem.
