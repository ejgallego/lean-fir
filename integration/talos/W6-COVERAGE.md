# W6 concrete-runtime coverage matrix

This is the operation-level audit companion to `PLAN.md`. “Heap theorem”
means a successful operation is related through `LiveHeapRel` or
`ConcreteRuntimeRel`; it does not imply W2 lowering composition or complete
failure correspondence. The matrix is intentionally conservative.

| `RuntimeOp` | Concrete executable | Successful refinement | Structured failures | W6.6 composition/artifact |
|---|---|---|---|---|
| `literal` | Naturals and UTF-8 strings | Tagged encoder, large-natural heap theorem, and fresh-string `LiveHeapRel` theorem with exact UTF-8 object decoding | Partial | Natural and string concrete hosts plus generated literal-`let` WPs and compiler-local writes; string whole-module Talos/Node/browser execution |
| `allocCtor` | Yes | Nonempty heap and tagged empty theorems | Partial; invalid-arity classification blocked by `FIR-BUG-wasm-none-constructor-arity-fault-classification` | Concrete Talos host plus arbitrary-arity generated constructor-`let` WP; certificate-free compiler/adaptor/evaluator inversion and arbitrary-continuation/finite-export correctness for mixed local and erased fields; whole-module concrete Talos execution; and Node/V8 plus browser-Worker checked-header execution |
| `objectProj` | Yes | Live and stale mapped-heap theorems | `expectedConstructor`, bounds, and dead-object source-address faults all exact | Concrete Talos host plus generated projection-`let` WP; certificate-free compiler/adaptor/resolver inversion derives the numeric operand/result locals, import, physical object word, and arbitrary continuation; exact source-classified constructor/bounds/stale-object traps with executable guards, whole-module concrete Talos execution, and successful/failing Node/V8 plus browser-Worker checked-slot execution |
| `usizeProj` | Yes | Live and stale mapped-heap theorems | `expectedConstructor`, bounds, and dead-object source-address faults all exact | Concrete Talos host plus generated projection-`let` WP; certificate-free compiler/adaptor/resolver inversion derives the i32 object operand, i64 result binding, and arbitrary continuation; exact source-classified constructor/bounds/stale-object traps with executable guards, whole-module concrete Talos execution, and compiler-shaped Node/V8 plus browser-Worker write/read execution |
| `scalarProj` | Four integer widths | Live packed-field and stale mapped-heap theorems | `expectedConstructor` and dead-object source-address faults exact for all four widths; live uninitialized-coordinate correspondence blocked by `FIR-BUG-wasm-none-uninitialized-scalar-projection` | Integer concrete host plus generated projection-`let` WP; certificate-free compiler/adaptor/resolver inversion derives the object operand, ABI-indexed result write, and arbitrary continuation while retaining one operation-specific concrete-read premise; exact constructor-kind leaves, a four-width deleted-object trap guard, and compiler-shaped `UInt8`/`UInt16`/`UInt32`/`UInt64` whole-module, Node/V8, and browser-Worker write/read execution; invalid hand fixture retains its exact external-engine failure under `FIR-BUG-wasm-none-scalar-slot-layout-contract`; floats tracked by `FIR-BUG-wasm-none-float-runtime-gap` |
| `cacheSet` | Typed concrete globals, recursive graph persistence, and Talos host | Constructive for every represented non-heap lane and mapped constructor, closure, box, natural, or string graph; public fuel and descriptor-table identity proved; general cache-set composition has no caller-supplied `CachePersistenceRefines` premise | Partial | Exact compiler/adapter cache shape, concrete hit/miss control, witness-indexed source/compiler judgment, zero-argument/singleton-result declaration-body package, empty-caller-tail proof lift, concrete return base rule, natural-, UTF-8-string-, and representation-polymorphic constructor-allocation declaration-body families with heap/witness growth, terminating declaration call, host call, both global writes, cached-value reload, local write, reusable miss-publication-to-hit facts, twice-called recursive cached constructor-graph whole-module execution, and Node/V8 plus browser-Worker miss/persistence/hit execution compose; remaining declaration-specific body-package families are incremental proof work; canonical dead-child gap fixed by `FIR-BUG-wasm-none-persistence-dead-child-refinement` |
| `partialApply` | Concrete Talos closure allocation | Heap theorem | Partial | Source interpreter, compiler/adapter, arbitrary-arity host call/local write, continuation, module-derived metadata tables, compiler-fold underapplication-body composition, ordinary/erased/multi-stage whole-module executions, and Node/V8 plus browser-Worker concrete closure allocation compose; `.tagged` result gap tracked by `FIR-BUG-wasm-none-partial-apply-tagged-result` |
| `closureApply` | Legacy callback excluded; generated trampoline uses metadata, capture projection, and direct calls | Not applicable as a runtime operation | Not applicable as a runtime operation | Complete compiler candidate enumeration/fold adaptation and execution after an arbitrary nonmatching prefix, capture/argument assembly, underapplication and saturated direct-call bodies, final result-local reload, concrete interprocedural judgment, body-WP-to-termination bridge, and ordinary/erased/multi-stage whole-module Node/V8 and browser-Worker executions compose |
| `closureMatches` | Concrete Talos metadata host | Exact match/nonmatch heap theorem | Partial | The complete compiler-generated nested matcher fold adapts and executes: nonmatches recurse, the first match selects its body, and later candidates remain unreachable; module-derived dispatch tables and ordinary/erased/multi-stage whole-module Node/V8 and browser-Worker executions cover the executable boundary |
| `closureProj` | Concrete Talos typed-capture host | Typed heap theorem | Partial | Recursive generated capture/argument assembly composes any projected fixed prefix with local arguments and either candidate body; module-derived descriptor tables and ordinary/multi-stage whole-module Node/V8 and browser-Worker executions cover the executable boundary, while erased captures correctly skip projection |
| `reset` | Yes | Tagged, persistent/nonunique fallback, and unique protocol theorems; one branch-independent successful refinement derives the selected case, exact frontier preservation, witness transport, and descriptor preservation | Dead-object source-address, unique-nonconstructor `expectedConstructor`, unique-constructor object-bounds, nonunique fallback decrement, and non-`expectedObject` recursively mapped child faults exact; release-fuel target traps are excluded across every mapped reset branch, with the erased child source mismatch separately carded | Concrete Talos host plus certificate-free `ResetSupported` compiler/adapter composition, exact unary call, reuse-token local write, arbitrary continuation, unique/nonunique whole-module executions, and unique/shared Node/V8 plus browser-Worker concrete execution; the ownership-strengthened direct family admits reset alongside every current pure external and ownership/tag/all-field-mutation effect without a tagged/fallback/unique certificate; fallback and recursive child-fault leaves preserve the exact delegated failure, while mapped host calls cannot emit the structured release-fuel target trap |
| `reuse` | Yes | Fresh empty/nonempty and in-place theorems; branch-independent operation and production-`let` theorems derive zero versus retained tokens from fitting capacity evidence, select tagged/fresh-heap/in-place execution internally, and return exact post-capacity, witness, descriptor, runtime/value, and header transport; fresh execution is constructed from a representation-sensitive allocation budget, retained execution preserves the frontier, and the production theorem returns the exact residual budget, local frame, and successor ordinary-token relation | Dead-object source-address and live-nonconstructor `expectedConstructor` faults exact; token/arity gates exclude earlier semantic faults; `reuseCapacitySafeProgram` excludes unknown or undersized retained tokens and exposes the in-place layout inequality; successful reuse preserves ordinary-token facts, while invalidation across unrelated intervening effects remains open as `FIR-BUG-wasm-none-reuse-retained-token-ordinary`; `OrdinaryPersistenceTransport` now states the exact safe-composition condition; provenance-sensitive empty-layout result-kind validation remains open as `FIR-BUG-wasm-none-reuse-retained-result-kind` | Concrete Talos host plus all three source/compiler/adapter branches, arbitrary-arity mixed token-local/local-or-erased-field call, descriptor transport, result-local write, arbitrary continuation, in-place/fresh whole-module executions, and in-place/fresh Node/V8 plus browser-Worker concrete execution; a generic arbitrary-arity trap combinator proves result-local write and continuation unreachable. `ReuseSupported` and `reuseLetStep_of_capacity` now reconstruct the production prefix, resolver contract, physical arguments, execution branch, result write, authoritative successor fact, fact relation, ordinary-token relation, local frame, and budget remainder without a certificate or target witness. `ReuseCapacityCodeEvaluates` lifts the law through arbitrary finite reuse-only spines, and `correctReuseCapacityCode` proves source observation plus actual generated-export termination with a refined return. `correctReuseBudgetedDirectPersistentIncrementCode` now covers the complete current `BudgetedDirectSupported` family plus reuse, compiler-erased persistent ownership effects, and successful ordinary increments; recursive decrement and remaining mutation families are the next facts-indexed instances, while the two shared-validator obligations remain for validator-wide admission |
| `box` | Five integer/USize kinds | Tagged and heap theorems | Partial | Witness-growing concrete host, source/compiler/adapter composition, exact unary call, object local write, maximum-`UInt64` whole-module execution, and Node/V8 plus browser-Worker heap-box/round-trip execution compose; the certificate-free indexed runtime law derives the canonical scalar lane from source/compiler typing and `StateRelated`, constructively selects immediate/promoted/heap representation from one fixed one-slot reservation, recovers the production call, and joins every mixed whole-export endpoint without target or allocation witnesses; floats share the runtime gap |
| `unbox` | Five integer/USize kinds | Tagged and heap theorems | `expectedScalar` and dead-object source-address faults exact; `.tobject` and supported-kind gates exclude the other semantic faults | ABI-indexed concrete host, representation-indexed source step, compiler/adapter, generated unary result call, exact i32/i64 local write, continuation, maximum-`UInt64` whole-module execution, and Node/V8 plus browser-Worker heap-box/round-trip execution compose; the certificate-free indexed runtime law consumes only source-state scalar-kind compatibility and reconstructs tagged/heap representation, descriptor match, checked read, production call, and destination write through `StateRelated`, preserving the complete budget/metadata frame and joining every mixed whole-export endpoint; floats share the runtime gap |
| `isShared` | Yes | Immediate, promoted, ordinary live-heap, and stale mapped-heap theorems | Dead-object source-address fault exact through `LiveHeapRel`, `ConcreteErrorSourceRel`, and the Talos host; remainder partial | Concrete object-like host, source step, compiler/adapter, generated unary result call, direct UInt8 local write, continuation, tagged/unique whole-module executions, and ordinary-object Node/V8 plus browser-Worker execution compose; the certificate-free indexed runtime law derives the production call and physical representation from source/compiler typing plus `StateRelated`, preserves the complete budget/metadata frame, and joins every existing mixed whole-export endpoint; the deleted-object guard and proof close `FIR-BUG-wasm-none-dead-object-fault-classification` |
| `objectSet` | Yes | Live and stale mapped-heap theorems, with exact frontier preservation on success | `expectedConstructor`, bounds, and dead-object source-address faults all exact with no post-state | Concrete two-i32 host, exact source-classified constructor/bounds/stale-object terminal leaves and stale no-write guards, FVar and erased-constant source steps, compiler/adapter, generated binary or local/constant call, continuation, whole-module mutation/readback including canonical erased zero, and Node/V8 plus browser-Worker checked-slot execution compose for every `LCNF.Arg` form and supported object-field kind; certificate-free FVar and erased effect laws derive their production prefixes and descriptor existence, then compose into the mixed ownership/tag/object whole-export endpoint |
| `usizeSet` | Yes | Live and stale mapped-heap theorems, with exact frontier preservation on success | `expectedConstructor`, bounds, and dead-object source-address faults all exact with no post-state | Concrete i32/i64 host, exact source-classified constructor/bounds/stale-object terminal leaves and stale no-write guards, source step, compiler/adapter, generated binary call, continuation, whole-module write, and compiler-shaped Node/V8 plus browser-Worker write/read execution compose; the certificate-free structural effect law derives production indices and the installed call, then joins object mutation in the mixed ownership/tag/field whole-export endpoint |
| `scalarSet` | Four integer widths | Live and stale mapped-heap theorems, including same-coordinate replacement, disjoint retained-field framing, and exact frontier preservation for every integer width | `expectedConstructor` and dead-object source-address faults exact for all four widths with no post-state | Concrete width dispatcher, one kind-indexed exact constructor-fault leaf, FVar source step, compiler/adapter, generated binary call, continuation, and compiler-shaped `UInt8`/`UInt16`/`UInt32`/`UInt64` whole-module, Node/V8, and browser-Worker write/readback compose; the certificate-free structural effect law derives production indices and resolver contract, consumes only a source/compiler layout judgment, and joins object/`USize` mutation in the mixed ownership/tag/all-field whole-export endpoint; repeated same-coordinate writes refine the source replacement filter and execute twice in one module; disjoint two-coordinate Talos modules for all four widths preserve the first coordinate after the second write; the four-width deleted-object guard checks exact traps and byte preservation; invalid hand fixture retains its exact external-engine failure under `FIR-BUG-wasm-none-scalar-slot-layout-contract`; floats share the runtime gap |
| `setTag` | Yes | Live and stale mapped-heap theorems, with exact frontier preservation on success | `expectedConstructor` and dead-object source-address faults both exact with no post-state | Concrete header host, exact constructor/stale-object terminal leaves and stale no-write guard, source step, compiler/adapter, generated unary call, continuation, whole-module case/readback, and Node/V8 plus browser-Worker header mutation compose; the certificate-free effect law derives production indices and the mixed ownership-and-tag whole-export theorem permits arbitrary successful tag mutations around the current direct/resident family; explicit wasm32 tag-fit premise retained |
| `inc` | Yes | Ordinary, tagged, and stale mapped-heap theorems | Dead-object source-address and unchecked tagged `expectedHeapReference` faults exact with no post-state; `.tobject` excludes `expectedObject` | Concrete ordinary/tagged/promoted host, exact stale-object and unchecked-tagged terminal leaves, source step, compiler/adapter, generated unary call, persistent elision, continuation, shared-reset whole-module execution, and balanced/shared-reset Node/V8 plus browser-Worker execution compose; ordinary wasm32 count-fit premise retained |
| `dec` | Yes | Complete recursive success and source-fault heap theorems for either outer check bit, every repetition, arbitrary constructor/closure child depth, and tagged representations | Mapped dead-object and `referenceCountUnderflow` faults are exact through arbitrary successful child/repetition prefixes; every positive unchecked tagged decrement preserves `expectedHeapReference`; zero amount is the specified empty-fold no-op; public mapped decrements exclude release-fuel target traps | Concrete checked/unchecked ordinary recursive host, checked tagged/promoted no-op, exact mapped stale/direct/recursive and unchecked-tagged terminal leaves, source step, compiler/adapter, generated unary call, persistent elision, continuation, checked and unchecked constructor-graph whole-module release, and balanced/recursive Node/V8 plus browser-Worker ownership executions compose with explicit closure-descriptor identity; mapped host calls cannot emit the structured release-fuel target trap |
| `delete` | Yes | Ordinary live/stale mapped-heap and erased-sentinel theorems, with exact frontier preservation on every successful lane | Dead-object source-address fault exact with no post-state; physical zero remains the delete-specific erased no-op; remainder partial | Concrete canonical-delete/erased-zero host, exact repeated-delete trap/no-write guard, representation-indexed source step, compiler/adapter, generated unary call, continuation, ordinary-object whole-module deletion, and exact dead-object Node/V8 plus browser-Worker execution compose without weakening ordinary object decoding; the certificate-free effect law and whole-export theorem derive production indices and permit arbitrary successful delete spines around the current direct/resident family |
| `getTag` | Yes | Complete `.tobject` constructor/tagged success theorem plus mapped stale-heap theorem | `expectedConstructor` and dead-object source-address faults exact through `LiveHeapRel`, `ConcreteErrorSourceRel`, and terminal case leaves; missing-alternative `invalidCases` transport is blocked by `FIR-BUG-wasm-none-unreachable-fault-classification` | Concrete Talos host plus generated constructor-case WP, exact constructor-kind and stale-discriminator leaves before alternative selection, whole-module concrete Talos execution, a direct allocate/delete/tag trap guard, and Node/V8 plus browser-Worker constructor-case execution |

Cross-cutting W6.5 state:

- compiler-level coverage is now tracked separately from operation coverage.
  `ConcreteSupportedExport` carries the actual compiler/adaptor body equation
  plus local-layout and runtime-call resolver alignment;
  `ConcreteSupportedExport.correctReturn` proves the certificate-free return
  base, while `correctNaturalLiteralReturn` proves the first allocating
  `let; return` composition through the exact generated four-instruction body,
  concrete heap/witness growth, and checked destination write.
  `CodeAdapted.let_eq` now inverts arbitrary direct-`let` compilation and
  adaptation into value/continuation fragments and the destination slot;
  `codeWP_naturalLiteralLet` uses that inversion to compose the same concrete
  literal step with an arbitrary verified compiler-selected continuation.
  `stringLiteralLet_eq`, `codeWP_stringLiteralLet`, and
  `correctStringLiteralReturn` close the equivalent UTF-8 `.object` lane
  through concrete allocation, resolver alignment, witness growth, and finite
  exported execution. The immediate-return theorem now derives concrete
  allocation success from aligned wasm32 `AllocationCapacity`; the reusable
  `AddressSpaceBudget.consume` law exposes exact remaining headroom for the
  forthcoming structural allocating spine.
  `codeWP_stringLiteralLet_of_budget` now performs the first recursive
  transport: one source-path budget constructs the allocation and its exact
  residual budget is passed to the generated continuation. The lower object
  and nonempty-constructor allocation boundaries expose the corresponding
  residual budgets as well. `DirectValuePathCost`,
  `DirectLetRuntimeRefinesWithCost`, and
  `codeWP_of_directValueEvaluates_withCost` lift this transport to the
  structural theorem. The contract harness checks arbitrary finite
  String-literal spines and arbitrary finite nonempty-constructor spines using
  one exact source-computed budget. Constructor nodes derive mixed
  local/erased physical arguments and concrete host steps internally.
  `BudgetedDirectSupported` additionally composes the allocating families
  with cost-zero aliases, immediate integer/`USize` literals, successful
  object, `USize`, and packed-integer scalar projections, integer boxing,
  compatible typed unboxing, and `isShared` in arbitrary finite
  interleavings. Each read-only instance records exact heap preservation and
  therefore retains the complete residual budget.
  `OwnershipBudgetedDirectSupported` adds successful reset only when the
  threaded frame also carries host/witness closure-descriptor agreement.
  Source/compiler admission remains branch-free; the semantic step and state
  relation derive tagged, persistent/nonunique fallback, or unique reset,
  exact frontier preservation retains the budget, and the strongest
  ownership/tag/all-field whole-export endpoint consumes the composed law.
  Successful reuse now has branch-independent operation and production-`let`
  theorems: fitting static evidence plus its dynamic relation determines zero
  versus retained execution and yields the exact validator-selected post fact.
  `FIR-BUG-wasm-none-reuse-retained-zero-empty-result` closes the previously
  missing retained-evidence/tagged-result relation case. The compiler theorem
  derives the mixed local/erased argument prefix, call and result slots, while
  the representation-sensitive constructor budget constructively covers
  zero-token allocation. The theorem threads the exact budget remainder,
  local frame, fact relation, and ordinary-token relation; successful reuse
  preserves ordinaryness even for aliases and fresh collisions. Structural
  whole-export composition now waits on ordinary-token invalidation across
  unrelated effects
  (`FIR-BUG-wasm-none-reuse-retained-token-ordinary`) and the coordinated
  provenance-sensitive result-kind fix
  (`FIR-BUG-wasm-none-reuse-retained-result-kind`).
  Natural literals are included through an exact three-way cost boundary:
  zero-byte wasm32 tagged immediates, aligned one-slot promoted tags, and
  aligned arbitrary-precision limb objects. The allocator theorem constructs
  the selected representation from frontier invariants and the path budget,
  then returns its exact remainder, so arbitrary finite Nat-literal and mixed
  spines require no allocation equation or representation witness.
  `ConcreteSupportedExport.correctBudgetedDirect` closes this fragment at the
  named-export boundary, pairing executable source evaluation with fuel-free
  concrete Wasm termination under `RefinedReturnPost`.
  `BudgetedSpineEvaluates` and
  `codeWP_of_budgetedSpineEvaluates` generalize the same induction to mixed
  direct/external spines. External nodes use the interpreter's exact
  three-step request/resume/bind protocol and a source-execution cost index,
  which can express response-dependent arbitrary-precision allocation.
  `correctBudgetedSpine` packages exact source trace execution and concrete
  export termination from reusable direct/external runtime laws. The pure-Int
  host boundary is now constructive: `integerAllocationBytes` gives the exact
  current header-plus-limb cost,
  `invoke_pure_integer_result_refines_of_budget` constructs the allocation,
  response, and extended witness, and `integerExternalStep_of_budget` exposes
  the resulting Talos host return and exact residual budget.
  `PureIntegerExternalSupported` and
  `externalLetRuntimeRefinesWithCost_pureInteger` now derive compiler-shaped
  calls selected by `PureIntegerExternalName` (`Int.ofNat`, `Int.neg`,
  `Int.add`, and `Int.sub`) through real argument compilation, adaptation,
  static external resolution, destination binding, exact source traces, and
  residual budget. `DirectLetRuntimeRefinesWithCost` now preserves the
  installed concrete external implementation; its generic invariant lift
  carries `IntegerResultRefines` across every current direct family.
  `correctBudgetedIntegerExternalSpine` therefore closes arbitrary finite
  direct/pure-integer interleavings at the named-export boundary without
  caller-supplied runtime laws or target witnesses.
  Pure natural results now have their own constructive boundary:
  `NaturalResultRefines` and
  `invoke_pure_natural_result_refines_of_budget` select the immediate,
  promoted-tag, or limb-object representation and construct the corresponding
  post-witness. `PureNaturalExternalSupported` admits `Int.natAbs`,
  `Nat.add`, and `Nat.sub`;
  `externalLetRuntimeRefinesWithCost_pureNatural` and
  `correctBudgetedNaturalExternalSpine` derive their compiler-shaped host
  steps and arbitrary finite direct/natural-result whole-export spines without
  target or representation witnesses. Decisions remain a separate scalar
  lane.
  That lane is now covered by the nonallocating `ScalarResultRefines` family:
  `PureScalarExternalSupported` admits `Int.decLt`, `Nat.decEq`, `Nat.decLt`,
  and `Nat.decLe` only as `.uint8`, and
  `externalLetRuntimeRefinesWithCost_pureScalar` plus
  `correctBudgetedScalarExternalSpine` derive zero-cost compiler-shaped calls
  and arbitrary finite direct/decision spines with unchanged heap budget and
  witness.
  `PureExternalSupported` now combines the integer, natural, and scalar
  source admissions. The external-step contract records exact preservation
  of the installed handler table, so generic invariant composition retains
  all three operation-family laws across every direct or external node.
  `correctBudgetedPureExternalSpine` closes arbitrary finite spines mixing all
  current direct operations with the ten current W7 resident numeric
  declarations, from one path budget and the three initially installed family
  laws.
  `BudgetedCodeEvaluates`, `CaseRuntimeRefines`, and
  `codeWP_of_budgetedCodeEvaluates` extend the same certificate-free induction
  through selected case nodes. The first constructive instance is
  `DefaultOnlyCaseSupported`: compilation erases the wrapper, and
  `correctBudgetedPureExternalDefaultCases` closes arbitrary nesting around
  mixed direct/resident-numeric code.
  `CaseResumptionStable` and `ExactReturnControlPost` make the generated arm
  boundary explicit. `SingleObjectConstructorCaseSupported`,
  `singleObjectConstructorCases_eq`, and
  `caseRuntimeRefines_singleObjectConstructor` derive and execute the
  production `getTag` test for a singleton object-constructor hit, while
  `correctBudgetedPureExternalSingleObjectConstructorCases` closes arbitrary
  nesting around the same direct/resident family.
  `ObjectConstructorCaseAltsSupported`,
  `objectConstructorCaseChainRefines`, and
  `caseRuntimeRefines_objectConstructorCases` generalize this to every
  normalized object-constructor chain, with or without one trailing default;
  `correctBudgetedPureExternalObjectConstructorCases` closes arbitrary chain
  length and nesting. `ScalarUInt8CaseAltsSupported`,
  `scalarUInt8CaseChainRefines`, and
  `caseRuntimeRefines_scalarUInt8Cases` close the parallel arbitrary scalar
  `.uint8` comparison family, deriving the dynamic tag range from
  `StateRelated`; `correctBudgetedPureExternalScalarUInt8Cases` closes
  arbitrary chain length and nesting without a host import.
  `EffectSupportedPredicate`, `EffectRuntimeRefines`, and the effect constructor
  of `BudgetedCodeEvaluates` extend the same induction through successful
  no-result effects without storing target evidence.
  `PersistentOwnershipEffectSupported` is the first constructive instance:
  production inversion recovers the continuation for compiler-erased
  persistent increment/decrement nodes, and
  `effectRuntimeRefines_persistentOwnership` preserves every invariant at zero
  budget. `correctBudgetedPureExternalPersistentOwnership` composes arbitrary
  such effects with default cases and the complete current
  direct/resident-numeric family.
  `OrdinaryIncrementEffectSupported` is the first generated-host-call
  instance. `CodeAdapted.inc_eq` derives numeric local/import slots and the
  continuation from production output; resolver alignment supplies the exact
  concrete contract; and the concrete increment theorem preserves the heap
  frontier and mapped capacities.
  `effectRuntimeRefines_ordinaryIncrement` retains the complete budgeted
  pure-external frame, while
  `correctBudgetedPureExternalOrdinaryIncrements` closes arbitrary finite
  interleavings with default cases and the direct/resident-numeric family.
  `ConstructorArgsCompiled`, `constructorArgsReady_of_compileArgs`,
  `constructorLet_eq`, `codeWP_constructorLet`, and
  `correctConstructorReturn` derive mixed local/erased argument code, physical
  operands, import/local layout, and compose constructor allocation with an
  arbitrary continuation or finite export. `localRuntimeCallLet_eq` and the
  three `codeWP_*ProjectionLet` rules now do the same static derivation for
  object, `USize`, and packed-scalar projections, including the physical
  object operand and arbitrary continuation; and
  `ConcreteCompilerCorrectnessContract.lean` checks that the public
  applications have no caller-supplied simulation premise.
  Successful semantic object and `USize` reads plus `ConcreteRuntimeRel`
  recover their constructor descriptor automatically; the object rule keeps
  only selected-field ABI-kind agreement, while the `USize` rule exposes no
  descriptor-readiness premise.
  `DirectValueEvaluates` and `codeWP_of_directValueEvaluates` now provide the
  first structural source-evaluation induction for arbitrarily long
  return/direct-value spines. The only step interface is the uniform
  `DirectLetRuntimeRefines` law over admitted declarations, compiler/adaptor
  outputs, and a preserved resource invariant. Zero-argument local aliases
  now construct that law from exact compiler ABI-kind agreement,
  compiler-resolved local bounds, a separately threaded exact frame-shape
  invariant, and `StateRelated`; a two-alias contract harness exercises the
  structural composition without supplying target instructions or indices.
  Read-only `USize` projections now construct the same law from source-only
  projection admission, production compiler/adapter inversion, the related
  physical object word, automatically recovered constructor descriptor,
  resolved concrete host contract, and the preserved frame-shape invariant.
  Object projections now add only a target-independent selected-field
  ABI-kind typing theorem; descriptor existence, concrete reads, physical
  words, and numeric target layout are derived. A generic runtime-law union
  composes aliases, `USize`, and object projection into arbitrary mixed
  read-only spines, and the harness supplies no target or descriptor witness.
  Discharging the law for scalar projection and allocation, then adding
  control-flow, calls, externals, caches, and faults, remains;
- the current UTF-8 string writer has exact byte readback and spatial-frame
  theorems; fresh allocation preserves the frontier/old heap and establishes
  `StringObjectRel`; exact-value descriptor binding preserves witness
  well-formedness and prior lookups; and fresh string allocation extends
  `LiveHeapRel` with exact checked decoding, descriptor-region disjointness,
  and a related `.object` result;
- globals, world, trace, successful external calls, and failed external calls
  have `ConcreteRuntimeRel`/trap boundaries; validated singleton-result source
  externals now also resolve to an executable concrete Talos host, decode and
  encode exact physical lanes, reject mismatched response lanes structurally,
  pass a whole-module UInt64 world/trace fixture, and compose the generated
  local-get/call/local-set prefix with the source interpreter's three-step
  external protocol, witness-extending concrete/source responses, the
  destination-local write, and arbitrary recursive continuations; the shared
  Node/browser concrete host executes the matching external artifact with the same
  return/world/trace, executes a twice-called cached external with exactly one
  effect, and separately verifies reject-by-default behavior;
- exact external source failures now have an arbitrary-arity terminal T4 leaf
  over the generated local-load/call/local-set sequence; the source and
  concrete implementations report the same `RuntimeFault`, and the
  result-local write plus continuation remain unreachable;
- source-fault preservation and target safety are audited separately in
  `W6-FAULT-AUDIT.md`. Target memory/layout/global/ABI failures cannot satisfy
  `ConcreteErrorSourceRel`; they require impossibility proofs under the
  runtime relation and explicit wasm32 resource premises;
- pure external responses now expose `ConcretePureExternalPost`: result
  allocation may extend the heap witness, while both worlds remain unchanged
  and each side's trace is exactly its previous trace plus the related call
  event. The theorem is independent of whether the result is a heap-backed
  `Nat`, `Int`, or `String`;
- compiler-generated closure dispatch now has one structural proof from the
  exact symbolic candidate enumeration through Talos adaptation and execution:
  any nonmatching prefix recurses, the first matching body executes, later
  candidates remain unreachable, and the final result-local reload resumes
  the surrounding suffix. Recursive capture/local argument assembly feeds
  both the concrete underapplication host and the saturated ordinary-Wasm
  direct-call boundary;
- arbitrary-precision heap integers have an experimental sign/magnitude
  allocation and checked-read boundary with exact positive/negative
  multi-limb round trips, frontier preservation, and old-prefix framing.
  Exact-value descriptors now extend `LiveHeapRel`; ownership, persistence,
  allocation framing, sharing, mutation exclusion, reset/reuse framing, and
  pure external `Int` responses preserve that relation. The layout remains an
  intentionally unstable experiment rather than a compatibility surface;
- the current `source-pretty-format-coverage` initial heap checks the
  compiler-derived packed `UInt8` coordinates `(1, 0)` for `Format.group` and
  `(0, 0)` for `Format.align` before emission; these checks are expected to
  move with compiler/layout improvements;
- `ConcreteError.toTrap` preserves source-vs-target classification and maps
  address-bearing dead-object and underflow faults back to semantic locations;
- mapped live-constructor object and `USize` projections preserve an exact
  semantic bounds fault through the checked reader, complete runtime relation,
  and Talos source-classified trap, including the original index and declared
  size;
- a common constructor-header refinement theorem exhausts immediate/promoted
  tags and every represented live heap shape; object, absolute-slot `USize`,
  and all four supported packed-scalar projections use it to preserve exact
  `expectedConstructor` faults through their generated terminal T4 leaves,
  before index, coordinate, or payload decoding;
- the matching object and `USize` setters preserve those exact source faults
  before either concrete or semantic state changes, and executable Talos guards
  reread the original payload after each trap;
- stale mapped references now use a source-address `deadObject address` trap;
  reusable `DeadCellRel` and `LiveHeapRel` lemmas plus the `isShared`, `getTag`,
  object-, `USize`-, and four-width scalar-projection Talos theorems preserve it
  against FIR's `deadObject location`, with `HeapReferenceRel` carrying the
  exact fault translation; stale object-, `USize`-, tag-, and four-width
  scalar-mutation, ownership, and repeated-delete theorems add the same
  no-post-state boundary (for positive-count `dec`; zero remains an empty
  fold); closed sharing and direct
  tag/projection/mutation guards cover execution, while the fixed
  classification is tracked by
  `FIR-BUG-wasm-none-dead-object-fault-classification`;
- invalid constructor arities are `malformed` in FIR but dedicated source
  `arityMismatch` faults in the concrete allocator; exact guards and the
  coordinated contract decision are tracked by
  `FIR-BUG-wasm-none-constructor-arity-fault-classification`;
- explicit `.unreach` and the no-alternative case fallback currently become
  the same native Talos `"unreachable"` trap with no structured host failure;
  this blocks their T4 leaves under
  `FIR-BUG-wasm-none-unreachable-fault-classification`;
- the raw one-field-reset/two-field-reuse counterexample still succeeds in FIR
  and trips the exact concrete `reuseAllocationTooSmall` capacity check, but
  `reuseCapacitySafeProgram` now rejects it from `WasmSupported`; fitting and
  shared-reset positive programs remain admitted; a dynamic capacity-value
  invariant now connects fitting retained evidence to the exact concrete
  allocation header, a whole-map invariant resolves every static fact at its
  compiler local, and the in-place reuse refinement derives its layout-fit
  premise from that bridge rather than accepting it independently; scoped
  header-capacity transport is instantiated for nonempty constructor
  allocation, empty immediate/promoted constructor allocation, both
  empty-token reuse allocation branches, actual in-place reuse, and unique
  reset; fresh nonempty constructor allocation additionally derives its exact
  checked heap/address result from static `ConstructorLayout` address-space
  capacity rather than an opaque successful-allocation equation; the
  production compiler/evaluator/state relation now also derives mixed
  local/erased word decoding and pointwise field refinement, eliminating the
  caller-supplied concrete step from recursive and finite nonempty-constructor
  compiler correctness;
  reset carries the retained constructor bound to its returned nonempty token;
- the full per-operation failure matrix is not yet proved; and
- natural and string literals, `allocCtor`, `partialApply`, `getTag`, `objectProj`,
  `usizeProj`, and all four supported integer `scalarProj` variants are
  composed with their W5/W2 generated case and `let` theorems using
  representation-aware concrete locals and host-owned memory; and
- lazy-cache hits and misses compose through the exact compiler/adapter shape,
  a zero-argument/singleton-result declaration-body package, its
  empty-caller-tail proof lift, the declaration-call termination boundary,
  typed host cache update, physical flag/value globals, generated result-local
  write, and reusable publication facts that feed the next hit; individual
  natural- and UTF-8-string-literal plus arbitrary-argument constructor
  allocation declaration bodies instantiate that package through a concrete
  return base rule and witness/state transport; constructor results retain the
  existing tagged-or-heap physical refinement rather than choosing a cache
  representation, while the remaining declaration families still need
  instances; scalar, erased/reuse, direct-tag, promoted-tag, and ordinary
  boxed/natural/string leaf roots discharge cache persistence constructively;
  ordered ownership folds, recursive constructor/closure steps, and the
  complete ordinary-live-count-bounded graph theorem, successful-fuel public
  lift, core global-write rule, and Talos host rule are constructive for every
  represented heap graph; canonical dead children are all-fuel no-ops and
  malformed dead headers remain target faults; and
- reference-count increment composes through exact object-like local widening,
  the concrete header/tagged operation, generated no-result host call, and
  persistent compiler elision; and
- checked and unchecked reference-count decrement compose through exact
  object-like local widening, the complete recursive ownership theorem,
  generated no-result host call, and persistent compiler elision; closure
  descriptor identity remains explicit; and
- explicit deletion composes through its exact physical value relation,
  canonical nonrecursive header release, and generated no-result host call;
  erased word zero remains an operation-specific no-op rather than an object;
  and
- `isShared` composes through immediate, promoted, and ordinary object
  representations, the exact direct UInt8 result lane, generated unary host
  call, destination-local write, and continuation; and
- all five supported integer/`USize` unbox variants compose through tagged or
  descriptor-matched heap representations, exact i32/i64 result lanes, the
  generated unary host call, destination-local write, and continuation; live
  non-box and stale mapped operands also terminate in the exact related
  `expectedScalar` and `deadObject` faults before that write or continuation;
  and
- all five supported integer/`USize` box variants compose through their exact
  source scalar and i32/i64 operand lanes, representation-dependent witness
  growth, the generated unary host call, object destination-local write, and
  continuation; and
- reset composes through one certificate-free direct law that derives its
  immediate, persistent/nonunique fallback, or unique protocol branch from
  source success and the state relation, transporting the representation
  witness, exact reuse-token local, descriptor agreement, and unchanged
  frontier through the generated unary host call and continuation; the
  ownership-strengthened whole-export theorem interleaves it with every
  current pure external and ownership/tag/all-field mutation effect;
  unique/shared Node/V8 and browser-Worker artifact execution composes; and
- reuse composes through fresh tagged, fresh heap, and in-place protocol
  branches, transporting the exact constructor descriptor across the generated
  token-plus-fields host call, result-local write, and continuation;
  in-place/fresh Node/V8 and browser-Worker artifact execution composes; and
- constructor-tag mutation composes through the exact object local, live-cell
  descriptor, concrete header writer, and generated no-result host call while
  preserving the constructor payload; and
- one-field object mutation composes through exact object/field locals, the
  constructor descriptor, checked concrete slot writer, and generated binary
  host call for the supported wasm32 object-field fragment; and
- `USize` mutation composes through the exact wasm32 object and Lean64 i64
  field lanes, checked concrete slot writer, and generated binary host call;
  and
- all four supported packed-integer mutations compose through their exact
  i32/i64 lanes and generated binary host calls; same-coordinate writes may
  replace any prior history at that coordinate, and a two-write module returns
  the second value; every supported integer write preserves retained scalar
  observations of every supported width when their byte intervals are
  disjoint, and corresponding two-coordinate modules reread the first value
  after the second write; each width crosses compiler-shaped whole-module,
  Node/V8, and browser-Worker mutation/readback execution; and
- a validated positional resolver now instantiates complete lowered Talos
  modules with the concrete host, derives its typed cache declarations from
  source initializers and its closure dispatch/descriptor tables from generated
  function order and first-use partial-application layouts, and executes closed
  fixtures through literals, constructor/case/projection, direct and recursive
  calls, ordinary/erased/multi-stage closure application, cache hit/miss
  publication, mutation, boxing, sharing, ownership, deletion, and reset/reuse
  plus a source external call without semantic handles; unsupported runtime
  families and malformed or non-singleton external imports fail during
  resolution; and
- a browser-safe external-engine host now mirrors the proved concrete word,
  header, slot, natural, constructor, closure, mutation, ownership, and reuse
  layouts and explicit foreign registry; the same frozen inventory of 41
  closed artifacts passes its live
  FIR oracle in Node/V8 and a Fetch-only browser Worker without runtime
  handles, including cache miss/persistence/hit, maximum-width heap
  boxing/unboxing, UTF-8 string allocation, and a mixed string/natural
  constructor graph, external world/trace effect, and cached external
  miss/effect/hit sequence; both engines also
  preserve the structured default external rejection and exact malformed-
  layout expected failure, with no remaining import-construction fragment
  gate; and
- the concrete external-engine host reserves and reconstructs the represented
  object-field constructor/natural `initialRuntime` subset before invocation,
  preserving all semantic locations and cell metadata; Node and the browser
  Worker audit a four-cell compiler-produced `List Nat` graph, its heap-backed
  entry-address round-trip, and its `getTag` result; they also reconstruct,
  audit, round-trip, and execute a compiler-produced Unicode string input,
  while packed constructors and other initial heap kinds retain explicit
  layout gates; and
- certificate-free finite compiler correctness now crosses arbitrary-length
  normalized concrete object and scalar-`UInt8` case control flow: production
  inversion derives the actual fallback, every branch/suffix target, and
  numeric indices; the recursive object theorem follows the source-selected
  hit/miss path through concrete `getTag`, while the scalar theorem follows
  the same path through direct local comparisons and derives its dynamic
  range from the value relation; and both whole-export theorems permit
  arbitrary chain length and nesting around the current direct and
  resident-numeric family; and
- certificate-free finite compiler correctness now also crosses arbitrary
  successful ordinary recursive decrements: production inversion derives the
  object local, decrement import, and continuation; resolver alignment supplies
  the exact unary concrete contract; recursive constructor/closure ownership
  release preserves the heap frontier; and an ownership-aware threaded frame
  carries immutable host/witness closure-descriptor agreement across every
  surrounding direct or pure-external node; and
- the same structural boundary now crosses arbitrary successful explicit
  deletions: source admission retains only lookup, semantic update, and the
  source-local compiler equation; production inversion and resolver alignment
  recover the generated unary call; both ordinary release and erased-zero
  no-op preserve the frontier exactly; and no descriptor-table premise is
  needed; and
- effect families now compose rather than remaining isolated endpoints:
  a general source-facing union theorem combines uniform operation laws that
  preserve one invariant, and the ownership endpoint permits persistent
  increment/decrement, ordinary increment, recursive decrement, and explicit
  delete in any order around the current direct/resident family; successful
  constructor-tag mutation now preserves that same ownership-aware frame and
  extends the mixed whole-export endpoint without target witnesses; successful
  FVar and erased object-field mutation now join it with descriptor existence
  recovered from the runtime relation and only slot-kind agreement left as a
  source typing premise; production inversion covers both the local/local/call
  and local/constant/call prefixes; successful `USize` mutation now supplies
  the same target-free structural boundary and exact frontier preservation,
  and composes with object mutation in the mixed whole-export theorem;
  successful packed `UInt8`/`UInt16`/`UInt32`/`UInt64` mutation now derives
  its kind-indexed production call and contract, consumes only a
  compiler-shaped source layout judgment, preserves the frontier exactly, and
  completes the mixed all-field whole-export endpoint; successful `isShared`
  now joins the budgeted direct family from source/compiler local typing
  alone, so every mixed endpoint admits sharing observations without a target
  index, concrete word, or operation witness; successful integer boxing now
  derives the scalar lane, concrete representation, allocation, production
  call, witness extension, and result write from source/compiler typing plus
  one fixed upper-bound reservation; successful typed unboxing now
  joins the same family from a source-state scalar-kind judgment, with
  descriptors, concrete reads, production calls, and exact physical lanes
  derived internally rather than supplied as certificates; and
- the remaining supported subfamilies still need whole-module or concrete
  external-engine coverage, while the wider generated Node/browser corpus
  continues to use the semantic JavaScript host runtime in parallel.

Update this table in the same commit whenever an operation crosses one of
these boundaries. A broad W6 completion claim requires every supported row to
be green through the final column, with exclusions tied to an explicit bug
card or documented fragment gate.
