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
arbitrary finite constructor spines use the same theorem. Mixed direct-value
composition now includes cost-zero local aliases and immediate integer/`USize`
literals plus successful object, `USize`, and packed-integer scalar projections
plus integer boxing, compatible typed unboxing, and `isShared` observations
through `BudgetedDirectSupported`. Boxing reserves one aligned
header-plus-slot upper bound and constructively covers immediate, promoted,
and heap representations; the immediate branch uses budget weakening because
it consumes no physical bytes. The read-only instances preserve the concrete
heap exactly and return the full residual address-space budget. Typed-unbox
admission exposes only a source-state scalar-kind compatibility judgment;
production output and `StateRelated` recover the concrete word, descriptor,
checked read, call, and exact i32/i64 result lane. Sharing admission needs only
source/compiler local typing. Successful reset composes through the
ownership-strengthened `OwnershipBudgetedDirectSupported` family:
`ResetSupported` contains only source/compiler local typing, while the
successful semantic step and `ConcreteRuntimeRel` derive the tagged,
persistent/nonunique fallback, or unique-constructor branch. Exact frontier
and descriptor-table preservation re-establish the ownership-aware indexed
frame, so reset interleaves with pure externals and every currently proved
ownership/tag/field-mutation effect without a branch certificate.
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
Lean 4.32 LCNF has no `Int` literal constructor, so integer construction enters
the next layer as ordinary external calls. `BudgetedSpineEvaluates` mixes
direct steps with exact three-step external source executions and carries a
Nat budget index; response-dependent external result allocation is therefore
expressible without target evidence. `ExternalLetRuntimeRefinesWithCost` is
the reusable implementation-law boundary, while
`codeWP_of_budgetedSpineEvaluates` and `correctBudgetedSpine` reconstruct the
compiler/adapter body and preserve exact external traces across arbitrary
mixed spines. `integerAllocationBytes` and
`allocateInteger_eq_ok_of_budget` now make the result-allocation half
constructive: the semantic `Int` fixes the current aligned heap extent, one
wasm32 source budget constructs the allocation and limb writes, and the same
proof derives metadata encodability plus exact residual headroom. Concrete
`ConcreteExternalImpl.IntegerResultRefines` is the reusable implementation
law, and `invoke_pure_integer_result_refines_of_budget` plus
`integerExternalStep_of_budget` construct the full concrete response, witness
extension, related result, Talos host return, and residual budget without
allocation or target witnesses. `PureIntegerExternalSupported` now admits
the explicit `PureIntegerExternalName` family: `Int.ofNat`, `Int.neg`,
`Int.add`, and `Int.sub`. Argument decoding, named-call inversion, static
external resolver alignment, and
`externalLetRuntimeRefinesWithCost_pureInteger` derive their complete
compiler-shaped external step without target witnesses. Lifting the existing
direct-operation laws through the installed-handler invariant is complete:
the strengthened costed direct law preserves `Host.externals`, the generic
lift threads `IntegerResultRefines`, and
`correctBudgetedIntegerExternalSpine` consumes both direct and pure-Int
families in one finite whole-export proof. The next external result family
now accounts for `Nat` independently of `UInt8`.
`NaturalResultRefines`, its constructive budgeted invocation and Talos-step
theorems, and `PureNaturalExternalSupported` cover the immediate,
promoted-tag, and limb-object cases under one existential post-witness.
`externalLetRuntimeRefinesWithCost_pureNatural` and
`correctBudgetedNaturalExternalSpine` instantiate that family for
`Int.natAbs`, `Nat.add`, and `Nat.sub`. The `UInt8` decisions form a
nonallocating scalar-result family. `ScalarResultRefines`,
`scalarExternalStep`, `PureScalarExternalSupported`, and
`externalLetRuntimeRefinesWithCost_pureScalar` instantiate that family for
`Int.decLt`, `Nat.decEq`, `Nat.decLt`, and `Nat.decLe`, with
`correctBudgetedScalarExternalSpine` closing the finite export. The structural
theorem itself did not need to change. The result families also compose: the
strengthened external runtime law exposes preservation of the concrete
handler table, `ConcreteBudgetedPureExternalFrame` retains the integer,
natural, and scalar implementation laws simultaneously, and
`PureExternalSupported` admits their source-facing union.
`correctBudgetedPureExternalSpine` consequently closes one arbitrary finite
whole-export proof whose source path mixes the full direct family and all ten
declarations in W7's current resident numeric surface.
Only the source evaluation, initial relation/frame, exact path budget, and
three operation-family laws cross the public boundary.
The finite structural theorem now also covers selected case nodes.
`BudgetedCodeEvaluates` records source branch selection without target
evidence, while `CaseRuntimeRefines` asks an operation-family theorem to lift
correctness of the selected compiled branch through the complete generated
dispatcher. `codeWP_of_budgetedCodeEvaluates` and
`ConcreteSupportedExport.correctBudgetedCode` compose that law with the
existing direct/external laws. The first instance,
`correctBudgetedPureExternalDefaultCases`, handles arbitrary nesting of
sole-default cases because production compilation erases each wrapper. This
is a theorem condition over compiler outputs, not a per-program certificate.
The first concrete dispatcher instance is now closed as well.
`CaseResumptionStable` states the precise arm-control condition, and the
structural induction retains `ExactReturnControlPost` until the outer function
boundary. `SingleObjectConstructorCaseSupported` admits a singleton object
constructor arm using only source/compiler facts plus a semantic tag-range
law. `singleObjectConstructorCases_eq` derives the exact test and indices;
`caseRuntimeRefines_singleObjectConstructor` composes the concrete `getTag`
contract; and
`correctBudgetedPureExternalSingleObjectConstructorCases` closes arbitrary
nesting of selected singleton hits. The first ordered multi-arm instance is
also closed. `TwoObjectConstructorDefaultCasesSupported` admits two object
constructor arms followed by a default using only source/compiler facts and
the semantic tag-range law. `twoObjectConstructorDefaultCases_eq` recovers all
three adapted branches and the nested tests;
`caseRuntimeRefines_twoObjectConstructorDefault` proves first hit, second hit
after one miss, and default after two misses. The second test requires a
nested generated resumption wrapper; `CaseResumptionStable.resume` derives
exactly that closure from the public stability premise.
`correctBudgetedPureExternalTwoObjectConstructorDefaultCases` exposes the
whole-export result. Generic compiler inversions now remove this arity bound:
`CodeAdapted.cases_eq` recovers the actual production fallback and chain;
`CaseChainAdapted.objectConstructor_eq` peels each executable test; and
`ObjectConstructorCaseAltsSupported` admits arbitrary normalized
constructor-only lists or one trailing default.
`objectConstructorCaseChainRefines` recursively follows `chooseAlt` under the
nested resumption law, `caseRuntimeRefines_objectConstructorCases` supplies the
uniform runtime condition, and
`correctBudgetedPureExternalObjectConstructorCases` exposes arbitrary chain
length and nesting at the whole-export boundary. The fixed-arity theorems
remain compatibility surfaces.
`CaseChainAdapted.scalarUInt8Constructor_eq` and
`caseChainWP_scalarUInt8_constructor` give the corresponding production
inversion and concrete direct-comparison rule for `.uint8` discriminators.
`ScalarUInt8CaseAltsSupported` admits arbitrary normalized constructor chains,
`scalarUInt8CaseChainRefines` follows the selected hit/miss path, and
`caseRuntimeRefines_scalarUInt8Cases` supplies the uniform runtime condition
without a host import or dynamic range premise.
`correctBudgetedPureExternalScalarUInt8Cases` exposes arbitrary scalar-chain
length and nesting at the whole-export boundary.
The structural theorem now has a parallel no-result effect boundary.
`EffectSupportedPredicate` keeps source evaluation target-free, and
`EffectRuntimeRefines` asks one reusable implementation theorem for each
admitted operation family. `PersistentOwnershipEffectSupported` admits the
compiler-erased persistent increment/decrement family;
`CodeAdapted.incPersistent_eq` and `CodeAdapted.decPersistent_eq` invert the
production compiler, while `effectRuntimeRefines_persistentOwnership` proves
the exact no-op simulation for every invariant.
`correctBudgetedPureExternalPersistentOwnership` therefore covers arbitrary
finite nesting and interleaving of these effects with default cases, current
direct operations, and resident numeric externals at unchanged allocation
budget.
The first generated-host-call instance now follows the same boundary.
`OrdinaryIncrementEffectSupported` carries only successful source increment
facts, the source-local ABI kind, and reference-count headroom.
`CodeAdapted.inc_eq` derives the exact unary prefix and continuation from
production output, `ConcreteSupportedExport.incrementCall` supplies the
resolver-selected host contract, and the strengthened concrete refinement
proves exact frontier preservation.
`effectRuntimeRefines_ordinaryIncrement` retains the complete budgeted
pure-external frame; `correctBudgetedPureExternalOrdinaryIncrements` exposes
arbitrary finite interleavings at the whole-export boundary. Subsequent
effect families should reuse this pattern rather than introduce
program-specific certificates.
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
   caches. Persistent ownership, ordinary increments, ordinary recursive
   decrements, and explicit deletion now instantiate the generic effect
   condition. The decrement
   endpoint uses `ConcreteBudgetedPureExternalOwnershipFrame` to carry exactly
   the host/witness closure-descriptor agreement required by recursive capture
   release; direct and external step interfaces expose independent table
   preservation, so the source admission remains target-free. Delete retains
   the ordinary frame and covers both live objects and the exact erased reset
   token with exact frontier preservation. `EffectSupportedOr` and
   `EffectRuntimeRefines.or` now combine these reusable laws;
   `OwnershipEffectSupported` and the corresponding whole-export endpoint
   allow persistent increment/decrement, ordinary increment, recursive
   decrement, and delete to occur in any order.
   `ConstructorTagEffectSupported` now adds successful `setTag`; production
   inversion and resolver alignment reconstruct its generated unary call, and
   exact frontier preservation retains the ownership-aware invariant.
   `OwnershipAndTagEffectSupported` and its whole-export endpoint therefore
   permit arbitrary interleavings of tag mutation with the ownership family.
   Successful FVar object-field mutation now supplies the same boundary:
   production inversion recovers both numeric locals and the binary call,
   semantic constructor success plus the runtime relation recover descriptor
   existence, and one universally quantified source typing premise connects
   the selected slot to the field kind. The mixed whole-export endpoint
   includes this family. The erased branch now has the complementary
   production inversion for its exact local/constant/call prefix; its
   target-free admission identifies the selected descriptor slot as erased.
   `ObjectFieldEffectSupported` combines both `LCNF.Arg` forms, and the mixed
   ownership/tag/object whole-export theorem consumes the uniform law.
   Successful `USize` field mutation now has the same structural boundary:
   production inversion recovers both numeric locals and its binary call,
   source admission carries only lookups/update, live bounds, and compiler
   equations, and exact frontier preservation retains the indexed budget.
   `FieldMutationEffectSupported` combines object and `USize` setters in the
   mixed whole-export theorem. Packed `UInt8`/`UInt16`/`UInt32`/`UInt64`
   mutation now completes that field family: production inversion and a
   narrow resolver theorem recover the kind-indexed binary call, while the
   source-only admission supplies retained-field separation, the
   compiler-shaped `size + usize` coordinate, and width-specific bounds.
   Exact frontier preservation retains the indexed budget, and the mixed
   whole-export theorem admits all integer setters. Float setters remain an
   explicit unsupported runtime fragment.
   Successful reuse is now branch-independent at both the operation and
   production-`let` boundaries. `reuseStep_of_capacityEvidence` derives zero
   versus retained execution from fitting static capacity evidence and its
   dynamic relation. `ReuseSupported` and `reuseLetStep_of_capacity` then
   reconstruct the actual mixed local/erased prefix, resolver call, result
   write, and authoritative successor fact. The zero-token branch is
   constructive from `constructorAllocationBytes`; no allocation result,
   representation branch, target index, or simulation certificate crosses
   the interface. The retained-zero empty-layout relation hole is fixed by
   `FIR-BUG-wasm-none-reuse-retained-zero-empty-result`.
   The production theorem now also returns the exact residual budget, local
   frame, and next ordinary-token relation. Fresh reuse spends the
   representation-sensitive constructor cost, while retained reuse preserves
   the heap cursor and therefore spends zero. Source reuse preserves every
   existing ordinary cell's persistence bit, introduces only ordinary fresh
   cells, and returns an object, so authoritative result-fact insertion
   preserves `ReuseTokenOrdinaryRel`.
   `ReuseCapacityCodeEvaluates` and
   `ReuseCapacityDirectLetRuntimeRefinesWithCost` now lift this step through
   arbitrary finite successful reuse-only spines. The strongest endpoint,
   `correctReuseCapacityCode`, proves the source returned observation and
   termination of the actual generated export with a refined return; its
   premises contain source evaluation and authoritative facts but no target
   code or translation certificate.
   The structural theorem is now generic in a facts-indexed operation-family
   runtime law. `OrdinaryPersistenceTransport` names the remaining
   source-runtime condition precisely, and the first mixed instance proves it
   reflexively for local aliases. `correctReuseAliasCode` consequently covers
   arbitrary finite alias/reuse interleavings. Each additional family can
   join by supplying the same ordinary-persistence condition together with
   its existing witness and retained-header transport.
   Immediate integer/`USize` literals, successful `USize`, object, and
   packed-scalar projections, compatible typed unboxing, and `isShared`
   observations now supply that proof as well.
   `correctReuseReadOnlyCode` covers arbitrary finite interleavings of reuse
   with the complete heap-preserving direct family.
   Nonempty constructor allocation now supplies both the source
   `OrdinaryPersistenceTransport` and its concrete capacity-result/header
   transport. `correctReuseReadOnlyConstructorCode` is the first allocating
   mixed whole-export endpoint.
   Integer boxing now joins this endpoint through
   `correctReuseConstructorBoxCode`; its immediate, promoted, and heap
   branches share one source ordinary-persistence theorem and one concrete
   retained-header transport.
   Natural and String literals complete the direct family.
   `correctReuseBudgetedDirectCode` covers the full
   `BudgetedDirectSupported` fragment plus reuse; the next widening obligation
   is ownership/effect composition.
   `ReuseCapacityEffectCodeEvaluates` and
   `correctReuseBudgetedDirectPersistentCode` now add source/target-identity
   persistent ownership effects.
   `correctReuseBudgetedDirectPersistentIncrementCode` adds successful
   ordinary increments: `incValue_ordinaryPersistenceTransport` establishes
   the source condition, while the existing concrete increment theorem
   supplies exact executable and mapped-header transport.
   `decLocationFuel_ordinaryPersistenceTransport` composes parent and child
   releases through the explicit source fuel, and
   `correctReuseBudgetedDirectOwnershipThroughDecrementCode` adds recursive
   decrement under the ownership-strengthened reuse frame.
   `correctReuseBudgetedDirectOwnershipCode` adds explicit deletion and now
   covers the complete `OwnershipEffectSupported` family.
   `modifyConstructor_ordinaryPersistenceTransport` and
   `ConcreteReuseCapacityOwnershipFrame.ofReplaceHeapEffectStep` isolate the
   reusable source and target transport boundaries for constructor mutation.
   `correctReuseBudgetedDirectOwnershipAndTagCode` instantiates them for
   successful tag writes, extending the facts-indexed whole-export theorem
   through `OwnershipAndTagEffectSupported`.
   `correctReuseBudgetedDirectOwnershipTagAndObjectCode` adds both FVar and
   compiler-erased object-field writes through the same transports and the
   existing descriptor-indexed production simulations.
   `setUSizeSlot_ordinaryPersistenceTransport` and
   `correctReuseBudgetedDirectOwnershipTagAndFieldMutationCode` add the
   absolute-slot `USize` setter through the same source/target boundaries.
   `setScalarField_ordinaryPersistenceTransport` and
   `correctReuseBudgetedDirectOwnershipTagAndAllFieldMutationCode` complete
   the current constructor-field family for packed
   `UInt8`/`UInt16`/`UInt32`/`UInt64` writes. Float setters remain outside the
   concrete runtime fragment.
   `ReuseCapacityBudgetedCodeEvaluates` and
   `codeWP_of_reuseCapacityBudgetedCodeEvaluates_exactReturn` now extend this
   facts-indexed induction through selected case nodes without carrying target
   evidence. The first whole-export instance,
   `correctReuseBudgetedDirectOwnershipTagAllFieldMutationDefaultCases`,
   permits arbitrary nesting of compiler-erased default-only cases around the
   strongest current direct/effect fragment.
   `correctReuseBudgetedDirectOwnershipTagAllFieldMutationObjectConstructorCases`
   and
   `correctReuseBudgetedDirectOwnershipTagAllFieldMutationScalarUInt8Cases`
   instantiate the same theorem for the two discriminating case families.
   Production compiler inversion reconstructs either the recursive concrete
   `getTag` chain or the import-free scalar comparison chain; both retain the
   exact facts and budget along the source-selected branch.
   The same relation now includes response-producing external `let` nodes.
   `ReuseCapacityExternalLetRuntimeRefinesWithCost` requires each external
   operation family to derive its production prefix, authoritative successor
   fact map, and post-frame from the source response and response-dependent
   cost. The generic structural and whole-export theorems consume that law.
   `ExternalLetRuntimeRefinesWithCostAndTransports` now exposes the common
   checked-local, witness, mapped-header, and source ordinary-persistence
   transports constructed by the concrete pure `Int`, `Nat`, and scalar
   implementation proofs. Their mixed operation-family theorem lifts to
   `ConcreteReuseCapacityPureExternalFrame`, and
   `correctReuseBudgetedDirectPureExternalDefaultCases` closes the first
   facts-indexed whole-export endpoint containing actual response-producing
   external calls.
   `correctReuseBudgetedDirectPureExternalObjectConstructorCases` and
   `correctReuseBudgetedDirectPureExternalScalarUInt8Cases` extend that mixed
   endpoint through both discriminating case families with unchanged facts
   and budget on branch entry.
   `EffectRuntimeRefines` now exposes exact installed-handler preservation,
   and its generic lifting theorem threads the three pure result laws across
   every proved no-result helper.
   `ConcreteReuseCapacityPureExternalOwnershipFrame` combines those laws with
   authoritative reuse facts, ordinary tokens, the exact byte budget, and
   host/witness closure-descriptor agreement. The direct, external-result,
   and complete ownership/tag/all-field-mutation families all preserve this
   one frame.
   `correctReuseBudgetedDirectPureExternalOwnershipTagAllFieldMutationDefaultCases`
   and its object-constructor and scalar-`UInt8` variants consequently cover
   arbitrary finite interleavings of all four currently proved structural
   node families without target evidence.
   `ReuseCapacityBudgetedCodeEvaluates` now also contains a source-only call
   constructor. `ReuseCapacityCallLetRuntimeRefinesWithCost` is its uniform
   implementation condition: it derives the production direct-call or
   closure-dispatch prefix and re-establishes the validator-selected fact map
   and complete residual frame. Existing endpoints instantiate the vacuous
   call family, so no earlier fragment is weakened.
   `BudgetedCapacityPreservingSuccessfulDeclaration` now states the exact
   hereditary callee result: execution/value correctness, ordinary-token
   persistence, witness/header transport, immutable handler/descriptor
   tables, and residual allocation headroom.
   `ConcreteReuseCapacityPureExternalOwnershipFrame.ofDirectDeclarationCall`
   turns that result plus compiler-derived argument assembly and local update
   into the full post-call frame.
   `DirectDeclarationCallImplementation.runtimeRefines` then reduces the
   generic call law to one recursive generated-program condition that selects
   this callee theorem from actual compiler/adapter output.
   `ReuseCapacityBudgetedCodeEvaluates.lazyLet` and
   `ReuseCapacityLazyLetRuntimeRefinesWithCost` now extend the same
   certificate-free induction to source-selected lazy-cache hit/miss paths.
   `BudgetedCapacityPreservingLazyStep` states their exact shared proof-side
   boundary, while
   `ConcreteReuseCapacityPureExternalOwnershipFrame.ofLazyCacheResult`
   reconstructs facts, ordinary tokens, locals, immutable tables, and residual
   budget once for both paths. The concrete hit is a zero-cost unchanged-store
   instance; the miss boundary consumes hereditary declaration and cache
   publication transports.
   `LazyCacheImplementation.runtimeRefines` reduces the remaining generated
   cache obligation to one environment-wide implementation condition.
   `BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet` now executes
   the exact generated declaration-call/`cacheSet`/two-global miss block
   instead of accepting a preassembled lazy simulation.
   `miss_of_budgetedDeclaration_cacheSet` composes that block with the
   budgeted hereditary callee theorem and threads all declaration transports
   into cache publication.
   `markPersistentFuel_preserves_heapCursor` and its concrete-global/Talos
   adapters now prove exact frontier preservation through recursive cache
   publication, so the miss theorem derives residual-budget preservation
   internally.
   Recursive persistence now also composes mapped-header capacity through
   every metadata write and child fold; the concrete global and Talos cache
   boundaries expose that theorem, so the miss constructor derives its
   publication-capacity transport from generated cache-slot facts.
   The remaining ordinary-token question is provenance-sensitive rather than
   an unconditional runtime invariant: a token aliasing the cached graph is
   invalidated when publication marks that graph persistent.
   `ReuseTokenOrdinaryBindTransport` now indexes the lazy-step theorem by the
   actual authoritative fact map and asks only for ordinaryness of facts that
   survive result-destination erasure. The all-location persistence theorem is
   a sufficient adapter rather than the cache contract, and an empty fact map
   is a proved conservative endpoint.
   `markPersistentLocationFuel_findCell_eq_of_not_reachable` now proves the
   missing graph frame: a recursive persistence traversal leaves every cell
   outside the original published ownership closure unchanged, including for
   cyclic and shared graphs. `ReuseTokenPublicationDisjoint` specializes that
   frame to retained tokens and yields the exact facts-aware binding transport
   through semantic `setGlobal`; empty facts and non-heap values are immediate
   instances. The executable miss constructor consequently asks for the exact
   source publication equation and graph disjointness rather than an opaque
   transport theorem.
   `PopulatedLazyCacheSlotRel` now supplies the previously missing relation
   between one semantic cache entry and its Wasm flag/value pair.
   Miss publication constructs that relation, while
   `hit_of_populatedSlot` derives the checked local update and post-binding
   state relation. `hit_of_compiledCache` fixes the exact production
   compiler/adapter program and cache indices. The uniform implementation law
   now receives the full reuse-capacity frame, including the local-frame
   bounds required by that write.
   `LazyCacheGlobalsRel` now lifts this relation across the complete generated
   cache table, rules out semantic entries without physical slots, and has an
   empty-state constructor specialized to the production adapter/Talos
   initial store. Its witness-aware transport theorem covers ordinary
   operations that preserve both global tables. A semantic lookup eliminates
   the empty branch, and `hit_of_compiledCacheTable` consumes the resulting
   physical lane at the exact generated indices.
   `SourceLazyLetResult.hit_cacheFacts` now derives that semantic lookup and
   the unchanged source runtime directly from the complete three-step hit.
   Internal-code and external miss branches are impossible because the third
   step cannot consume both the cache and caller-binding frames.
   `hit_of_compiledCacheTable` therefore no longer accepts a caller-supplied
   cache-presence premise; the contract harness fixes this source-only
   inversion boundary.
   `LazyCacheGlobalsRel.publish` now proves the pointwise miss-publication
   update. Semantic absence yields the old zero flag; initializer uniqueness
   and the even/odd physical layout preserve every other source/target slot.
   `withPublishedCacheTable` packages the updated table with the exact
   budgeted miss result.
   `ConcreteReuseCapacityCacheFrame` now carries the table alongside the
   canonical reuse, pure-external, and ownership invariants.
   Its exact lazy-result reconstruction accepts one path-specific cache
   transition, and the strengthened uniform `LazyCacheImplementation` returns
   the successor table. `adaptedInitial` establishes the augmented entry
   frame. The validator's Boolean uniqueness check is proved equivalent to
   `List.Nodup`. `LazyCacheInitializerSignatures` isolates the validator's
   singleton-result loop, and `LazyCacheTableLayout.ofSignatures` derives the
   exact paired physical layout from the executable global-kind fold.
   `LazyCacheValidationFacts` packages signatures and Boolean uniqueness
   inside the table invariant, eliminating separate layout and uniqueness
   premises from initial construction and publication.
   Coordinate one integration-owned validator proof accessor constructing
   `LazyCacheValidationFacts` from successful validation.
   `FIR-BUG-wasm-none-lazy-source-step-count` is fixed by the shared
   `SourceLazyMissResult` relation. It separates staging, cache-miss entry,
   arbitrary finite isolated callee execution, publication, and binding.
   `ExecSteps.withFrameSuffix` lifts the isolated execution under the protected
   cache and caller-bind frames, ruling out witnesses that consume or
   reconstruct caller frames, while
   `SourceLazyLetResult.execSteps` preserves the generic finite-prefix API.
   `SourceLazyLetResult.miss_cacheFacts_of_valueEq` derives initial lookup
   absence and the exact semantic publication. The generated miss theorem now
   derives its zero physical flag from that absence and the whole-table
   relation. The paired `cachedHeapFourStepsRemainInCallee` and
   `cachedHeapSevenStepsPublishAndResume` guards retain the old counterexample
   and validate the repaired protocol.
   `SourceCodeResult` now retains the complete terminal runtime of a source
   body and erases to the former observation-facing theorem.
   `SuccessfulDeclaration` carries that exact result, and
   `ConcreteCodeSimulation.sourceResult` constructs it across every supported
   structural node. `ExecSteps.final_eq_of_done` is the general deterministic
   finite-run theorem used to identify exact terminal states without adding
   globals or the allocation frontier to `Observation`.
   `SourceLazyLetResult.miss_cacheFacts_of_callee` aligns the structured
   miss's isolated body with the hereditary declaration theorem from static
   source lookup/parameter/body equations. The budgeted generated miss now
   derives its publication runtime equation instead of accepting it, while
   permitting unrelated nested cache evolution.
   Empty whole-table slots now retain physical presence of the unconstrained
   value lane as well as the zero flag. `slotLanesPresent` derives both
   generated write bounds from the invariant, and `publish` overwrites either
   an empty slot or one populated by nested execution. The concrete host
   cache write preserves physical Wasm globals; `afterCacheSet` transports the
   evolved pre-publication table across that host step, and
   `withCacheSetPublishedTable` constructs the exact successor table after the
   generated value/flag suffix without assuming the selected slot stayed
   empty.
   `LazyCacheGeneratedEnvironment` now packages ordered context/module
   cache-name equality, checked initializer facts, and exact generated
   cache-operation/result-signature kind equality.
   `LazyCacheGeneratedEnvironment.select` derives the emitted initializer and
   signature facts from the compiler's actual `findIdx?` result.
   `hit_of_compiledCacheTable` and
   `miss_of_budgetedDeclaration_cacheSet` consume that one static environment
   rather than independent per-call lookup/signature premises, and
   `LazyCacheImplementation` retains the environment once for the whole
   generated program.
   `miss_of_cachedDeclarationFrame` now lifts the hereditary miss to the
   canonical program invariant. It derives the concrete host result, evolved
   physical-lane bounds, both Wasm global writes, the destination-local write,
   and immutable host tables instead of accepting those execution artifacts
   from the declaration environment.
   `ConcreteGlobals.staticLayout` now records the ordered static name/kind
   table independently of cached values. Declaration is exact, concrete
   global writes preserve it, and `cacheSetStep_preserves_hostStaticLayout`
   lifts that result through the executable host call.
   `LazyCacheGlobalsRel` retains the canonical
   `host.runtime.globals.staticLayout = cacheDeclarations source` equation
   from production initialization through host and Wasm publication.
   Singleton initializer signatures show that `cacheDeclarations` preserves
   the exact initializer-name order; checked initializer uniqueness therefore
   lets `hostSlot` derive the selected concrete slot and kind.
   `miss_of_cachedDeclarationFrame` no longer accepts `cacheFound` or
   `cacheKindEq`. Its remaining work belongs to the recursive generated
   declaration-environment induction, not another runtime cache premise.
   Successful cached nullary lowering and Talos adaptation now have joint
   production inversions: `compileCachedLetValue_adapted_inv` recovers the
   cache index, declaration/runtime call indices, symbolic code, and
   executable target code from the two actual pipeline success equations.
   The generic source-hit inversion derives the unchanged runtime and semantic
   cache lookup without constraining binder metadata.
   `BudgetedCapacityPreservingLazyStep.hit_of_compiler` composes those facts
   with local-layout alignment, the generated cache environment, and the
   canonical runtime frame, yielding the exact zero-cost hit, checked result
   write, reuse-fact erasure, and successor cache relation. Thus the uniform
   hit branch is structural and target-certificate-free; the remaining cache
   induction work is the hereditary miss/publication branch.
   The common `LazyCacheCallSupported` relation now names only source nullary
   admission and destination ABI facts; its internal-miss specialization adds
   only the selected source body. `ConcreteSupportedExport.cacheSetCall`
   recovers the exact resolved publication import contract and arities from
   the compiler-selected runtime call. The recursive
   `LazyCacheInternalMissInduction` is indexed by the declaration call chosen
   by production adaptation and returns the hereditary cache-aware callee
   theorem plus facts-aware publication transport.
   `miss_of_supportedExportCompiler` composes those facts into the exact
   budgeted miss and successor cache relation without accepting a target
   execution, numeric call index, concrete value, import contract, or local
   layout certificate. Internal miss composition is therefore closed; the
   remaining global construction obligation is the existing
   `FIR-BUG-wasm-none-reuse-retained-token-ordinary` publication transport,
   while external nullary misses deliberately remain a separate hereditary
   external-result branch.
   `LazyCacheInternalSupported` now packages the source-only hit/miss family
   consumed by the structural proof. Its constructors retain source admission
   and recursive cost but no target code, indices, values, stores, witnesses,
   or executions.
   `LazyCacheInternalCalleeInduction` factors the hereditary declaration
   theorem from its source postcondition. The preferred
   `LazyCacheInternalPublicationInduction` instantiates that postcondition
   with authoritative retained-token disjointness from the published
   ownership closure and constructively derives the former publication
   transport. The weaker hereditary theorem suffices without alias analysis
   whenever the returned value is a non-heap reference.
   `LazyCacheInternalDeclarationInduction` lifts this condition uniformly
   over every admitted internal miss and canonical cache frame. It is a
   recursive module theorem rather than a call-site target certificate.
   `LazyCacheImplementation.ofInternalCompiler` composes it with the
   compiler-derived hit and miss branches, and
   `ConcreteSupportedExport.internalLazyRuntimeRefines` exposes the exact
   facts-indexed runtime law consumed by the generic structural code theorem.
   `PhysicalValueRel.isNonHeapReference_of_kind` now derives source
   publication safety for every exact ABI result except `.object` and
   representation-polymorphic `.tobject`. Exact tagged, erased, reuse-token,
   integer-width, and scalar results therefore need no alias theorem.
   `LazyCacheInternalHereditaryDeclarationInduction` isolates the ordinary
   recursive generated-declaration theorem before publication reasoning, and
   `LazyCacheInternalResultKindsNonHeap` records the source-only fragment
   policy. Their `ofHereditaryNonHeap` adapter constructs the complete
   publication-aware declaration induction, while
   `internalNonHeapLazyRuntimeRefines` exposes the resulting compiler cache
   law.
   The corresponding executable contract guard confirms
   `FIR-BUG-wasm-none-lazy-cache-result-refinement`: strict
   `.object`-to-`.tobject` named-call refinement is admitted by the source
   checker, but current lazy lowering emits caller-kind cache instructions
   against a declaration-kind value global, so the production adapter rejects
   the generated module. Coordinate the shared lowering repair before
   deriving exact kind alignment from supported compiler output; do not weaken
   W6's exact typed-lane relation.
   `ReuseCapacityBudgetedCodeEvaluates.sourceResult` now retains the exact
   terminal source runtime for the complete mixed structural judgment.
   `ReuseCapacityCodeEntryTransports` collects witness, header-capacity,
   ordinary-persistence, external-table, host-descriptor, and
   witness-descriptor preservation from one execution entry; its `refl` and
   `step` theorems provide the complete transport algebra.
   `ReuseCapacityEntryRelativeFrame` pairs those facts with any existing
   facts-indexed frame, and
   `codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelative` specializes
   the certificate-free structural proof to that frame. Its conclusion now
   returns the exact source result, target `CodeWP`, final base frame, and all
   six entry-to-exit transports.
   `ReuseCapacityBudgetShiftedFrame` now makes every indexed frame parametric
   in fixed caller-owned budget slack. The `shiftBudget` adapters for direct,
   external, call, lazy, and effect runtime laws preserve that slack across
   every costed or cost-neutral operation family.
   `codeWP_of_reuseCapacityBudgetedCodeEvaluates_withSlack` therefore starts
   at `requiredBytes + slack` and returns the final frame at `slack`, while
   `codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelativeWithSlack`
   returns that residual frame together with the exact source result, target
   `CodeWP`, and all six entry transports. This discharges the hereditary
   declaration contract's residual-budget uniformity requirement without
   target determinism or target-execution certificates.
   The transport-strengthened pure-external boundary now also exposes exact
   preservation of semantic globals, physical Wasm globals, and the concrete
   host cache layout. Its
   `reuseCapacityEntryRelativeCache` theorem transports the whole generated
   cache table, rebuilds the canonical ownership frame, and composes all six
   entry transports. The production
   `reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache`
   theorem closes the pure `Nat`/`Int`/scalar external family for hereditary
   cached bodies without adding target evidence.
   `DirectLetStepTransports` now packages the witness, header-capacity,
   ordinary-persistence, semantic-global, physical-Wasm-global, and concrete
   host-layout facts produced by every successful direct operation.
   The facts-indexed direct law retains that package through disjunction,
   external-table, descriptor-agreement, budget-shift, and structural-code
   adapters. Every production direct producer constructs it: readers use
   reflexive or failure-clearing transports, while boxing, literals,
   constructors, and reuse use their allocation/rewrite transports.
   `ReuseCapacityDirectLetRuntimeRefinesWithCost.reuseCapacityEntryRelativeCache`
   transports `LazyCacheGlobalsRel`, reconstructs the complete cache frame,
   and composes the entry relation. Its production
   `reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache` theorem and
   contract guard close the complete current direct family without target
   evidence.
   `RuntimeStepTransports` now names the cache-neutral representation facts
   shared by direct and effect operations.
   `EffectStepTransports` adds both descriptor-table equalities, while
   `EffectRuntimeRefinesWithTransports` composes the package uniformly through
   every admitted source effect family. Persistent ownership, increment,
   recursive decrement, deletion, tag mutation, both object-field forms,
   `USize`, and every supported packed-scalar mutation all construct that
   package from their production compiler/runtime proofs.
   `EffectRuntimeRefinesWithTransports.reuseCapacityEntryRelativeCache`
   transports the complete cache table and extends the fixed-entry relation.
   Its production
   `effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache`
   theorem and contract guard close the current no-result effect family
   without target evidence.
   The endpoint-exact `ofDirectDeclarationCallExact` theorem retains the
   hereditary callee's actual post-store and witness.
   `DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative`
   consumes the callee's evolved `LazyCacheGlobalsRel` and composes its six
   representation transports from the fixed entry.
   `LazyCacheImplementationWithEntryTransports` similarly augments the
   compiler-derived hit/miss implementation with a source ordinaryness
   transport. Hits are identities; current non-heap misses compose the
   hereditary callee transport with heap-neutral semantic publication.
   The production
   `internalNonHeapLazyRuntimeRefines_entryRelativeCache` theorem and its
   contract guard close the current internal lazy family without an
   unchanged-global premise.
   Next derive the cache-aware direct-call implementation uniformly from
   production declaration selection, including admitted saturated closure
   dispatch, and construct
   `LazyCacheInternalHereditaryDeclarationInduction` recursively for the
   generated declaration environment. Do not reintroduce a
   `ConcreteCodeSimulation`, `ReuseCapacityCodeSimulation`, or call-site
   target execution premise.
   Heap-valued `.object`/`.tobject` publication cannot preserve the current
   all-location `OrdinaryPersistenceTransport`; extending that fragment
   requires a deliberately weaker entry invariant or coordinated alias/fact
   invalidation in addition to `ReuseTokenPublicationDisjoint`. External
   nullary declarations remain a separate hereditary external-result branch.
   Integration must still expose the universal validator accessor needed to
   discharge `LazyCacheValidationFacts` for every successfully validated
   module.
   Before unrestricted mixed programs can retain reuse facts across unrelated
   effects, coordinate stable ordinary-token provenance
   (`FIR-BUG-wasm-none-reuse-retained-token-ordinary`) and the
   provenance-sensitive `.tobject` result-kind condition
   (`FIR-BUG-wasm-none-reuse-retained-result-kind`). Reuse the existing W6
   operation lemmas for later effect families, but do not expose
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
   Successful reuse no longer requires a caller-selected representation
   branch at the operation layer. Its remaining structural obligations are
   constructive allocation headroom, ordinary-token provenance, and the
   shared result-kind gate, not an execution certificate.
   Structured unreachability remains the shared-contract blocker.
7. Add a target relational execution/adequacy layer and prove finite-prefix
   preservation, divergence preservation, and then weak simulation or weak
   bisimulation as useful.
8. Let W7 generation proceed independently against the current concrete
   runtime surface, then prove T5 per internalized runtime function.
9. Close with T6 and the pure `prettyM` acceptance theorem.
