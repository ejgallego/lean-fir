# FIR WebAssembly and Talos plan

This document is the source of truth for the WebAssembly track on branch
`wasm/talos-runtime`. Work takes place in `.worktrees/wasm-talos` under the
parallel-development rules in `AGENTS.md`.

The track owns `Fir/Wasm/`, `integration/talos/`, and Wasm-specific bug cards.
Changes to the semantic Wasm ABI are shared-contract changes: isolate them in
their own commit, describe their effect on both tracks, and coordinate landing
them through the integration owner before dependent work continues.

## Goal

Relate executions of final impure LCNF to executions of generated WebAssembly
in Talos. The first target is a semantic backend with an abstract host runtime;
a later refinement will replace that host model with a concrete linear-memory
runtime.

```text
final impure LCNF
        |
        | Fir.Wasm.lower
        v
FIR symbolic Wasm -- static checker --> Talos Wasm.Module
                                              |
                         +--------------------+--------------------+
                         |                                         |
                  semantic host runtime                later linear-memory runtime
                         |                                         |
                         +------------ refinement proof -----------+
```

This layering separates three claims:

1. LCNF is lowered to the intended Wasm control and data flow.
2. Runtime imports implement their abstract FIR operations.
3. A concrete memory layout refines the abstract runtime.

The first proof should establish claims 1 and 2 without prematurely fixing a
production heap layout.

## Current status

- W0 is complete: the semantic ABI, checked kinds, stable imports, opaque
  handles, target failures, and supported-fragment guards are in place.
- W1 is complete: FIR validates the generated symbolic subset before
  adaptation, Talos validation is an additional guard, and function origins
  survive conversion.
- W2 is complete for natural/string literals, constructor allocation, object
  projection, and constructor tags. The positional host resolver, typed codec,
  structured source/target traps, abstract contracts, and executable Talos
  guards live under `integration/talos/FirTalos/`.
- W3 is complete: `runDifferential` runs both semantics, encodes entry
  arguments, classifies all Talos outcomes, and compares outcome, world,
  trace, and the canonical reachable heap. Its result carries field-level
  mismatch evidence.
- W4 proof infrastructure is in place: coherent handle-codec round trips,
  scalar lane lemmas, adapter signature/local/label/call preservation,
  positional host satisfaction, and fuel-free observation postconditions.
  The adapter recursion is now terminating and transparent to proofs.
- W4 layer 4 now has local lowering and source/host simulations for natural
  and string literals, constructor allocation, object projection, and tag
  lookup. Successful handle encodings preserve a chainable coherence/freshness
  invariant, and checked `UInt32` tag bounds make case comparisons injective.
  Exact successful host steps have a common instruction-level Talos `wp`
  lifting through abstract host contracts, with specialized literal rules.
  Target handle-space availability is an explicit premise rather than an
  implicit infinity assumption.
- Generated constructor and projection call stacks now instantiate that common
  `wp` rule. The complete adapted `local.get; getTag; const; i32.eq; if`
  sequence selects the same constructor arm as the source `Nat` comparison,
  including restoration of the operand tail across both arms. Completing that
  proof exposed and fixed the missing allocation-side constructor-tag bound;
  both allocated and compared tags are now checked before narrowing to `i32`.

The next W4 slice composes these generated-stack rules recursively over the
call-free code fragment, starting with straight-line `let`/`local.set` chains
and then the recursive case chain. That result can then be lifted through
`RelatedPost` to whole exported functions. The adapter still rejects
initializers and closures.

An independent artifact lane, A0, may proceed in parallel with W4. It turns
the already checked semantic module into a standards-consumable host-backed
Wasm artifact and runs the W3 corpus in an external engine. A0 does not define
the production linear-memory ABI and must consume, rather than modify, the
frozen semantic ABI and supported-fragment boundary.

## Architecture decisions

### Two-level type information

Do not use a physical Wasm type as the only description of an LCNF value.
Several semantically different values share the same stack representation.
Introduce an ABI kind along these lines:

```lean
inductive AbiKind
  | object | tagged | tobject
  | erased | reuseToken
  | uint8 | uint16 | uint32 | uint64 | usize
  | float32 | float
```

The physical representation is derived afterward:

| ABI kind | Semantic Wasm representation |
|---|---|
| object, tagged, tobject, erased, reuse token | `i32` handle or sentinel |
| `UInt8`, `UInt16`, `UInt32` | `i32` |
| `UInt64`, semantic `USize` | `i64` |
| `Float32` | `f32` |
| `Float` | `f64` |
| void | no stack value |

Keeping semantic `USize` as `i64` matches FIR's current abstract runtime. This
is the semantic ABI, not yet a claim about a production wasm32 pointer ABI.
A later target-specific refinement can map `USize` to wasm32 `i32` with the
appropriate source-side word-size semantics.

Function parameters, locals, results, runtime operations, and imports must
retain `AbiKind`. Physical Talos signatures are projections of that metadata.
Unknown impure types must be rejected instead of silently defaulting to `i32`.

### Opaque handles

Use `i32` as an opaque handle into host-managed values, rather than encoding
FIR heap locations or tagged payloads directly. A first host state should be:

```lean
structure RuntimeHost where
  runtime : Fir.LeanIR.Impure.RuntimeState
  handles : HandleTable
  fault? : Option Fir.LeanIR.Impure.RuntimeFault
```

The handle table should reserve a sentinel, intern equal object-like values,
preserve aliases, allocate deterministically, and report exhaustion as a
target resource failure. Host operations decode handles, reuse the FIR runtime
operations, and encode results back to Wasm values.

Keeping the structured fault in host state allows a Talos trap to be related
to `RuntimeFault` without making theorem statements depend on trap strings.

### Closures are a separate gate

Talos host functions cannot call back into a Wasm-defined function. Therefore
the current `closureApply` import cannot be the final implementation of LCNF
closures: delegating it to the FIR interpreter would make the backend theorem
circular.

The first correctness fragment excludes `pap` and closure-valued `fvar`
applications. Before enabling them, choose and document one real dispatch
design:

- a function table plus `call_indirect` and typed wrappers;
- a uniform boxed calling convention and dispatcher; or
- a Wasm-level trampoline protocol.

The choice must specify heterogeneous captured values, oversaturated calls,
recursive targets, and the representation of fixed arguments.

### Initializers are explicit work

`Fir.Wasm.Module.initializers` is currently ignored by the Talos adapter. Do
not silently map every zero-parameter declaration to a Talos start function.
First decide whether the semantic backend uses:

- explicit initialization invoked by the harness;
- a generated aggregate start function; or
- source-compatible lazy global evaluation.

Until then, the proved fragment excludes programs whose behavior depends on
global initialization or lazy caching.

### Validation belongs to FIR

Talos's current `Module.validate` is deliberately partial and accepts control
flow or instructions its stack checker does not model. Add a complete checker
for FIR's generated symbolic subset. It must cover:

- unique parameters, locals, join labels, declarations, and exports;
- local and label resolution;
- operand-stack ABI kinds through every symbolic instruction;
- call arguments and results;
- block, branch, case, and return stack shapes;
- import ordering and runtime-operation signatures; and
- initializer and entrypoint restrictions for the current fragment.

A successful Talos validation remains a useful additional test, but is not the
well-formedness premise of the correctness theorem.

## Work breakdown

### W0: freeze the semantic ABI

This is the serial gate for all later work.

Deliverables:

- add `f32` and `f64` physical types;
- introduce `AbiKind` and total checked conversion from impure `Expr` types;
- retain ABI kinds in locals, signatures, imports, and runtime operations;
- specify erased, void, tagged, tobject, and reuse-token encodings;
- define deterministic runtime-import identities and ordering;
- define handle encoding and decoding relations;
- define target resource failures and structured traps;
- introduce an explicit `WasmSupported` or `AbiWellFormed` predicate; and
- add guards for every impure type and runtime-operation signature.

Cross-track dependency: FIR's abstract scalar runtime does not yet model
`Float` or `Float32`. Record the gap and coordinate any shared runtime change
through the integration owner; do not create a private Wasm-only source value.

Definition of done:

- no known impure type silently maps to the wrong physical type;
- encode/decode round trips are tested for every supported ABI kind;
- aliases retain stable handles;
- every runtime operation has a checked semantic signature; and
- `make check` passes in the worktree.

### W1: harden the adapter and checker

This can proceed in parallel with W2 after W0 is frozen.

Deliverables:

- implement the complete symbolic checker;
- preserve a source map from Talos indices to FIR imports/functions;
- check import and function index resolution;
- check local and label depth conversion;
- reject unsupported initializer and closure cases explicitly;
- run Talos's validator as an additional smoke check; and
- add negative fixtures for unknown locals, labels, calls, and bad stack
  shapes.

Definition of done:

- every module accepted by the adapter first passes FIR validation;
- malformed symbolic fixtures fail with specific errors; and
- adapter tests cover imports, direct calls, nested blocks, cases, and jumps.

### W2: implement the first semantic host runtime

Start with the operations required by constructor control flow:

1. natural and string literals;
2. constructor allocation;
3. object projection; and
4. constructor tag lookup.

Deliverables:

- `Codec.lean` for typed value/handle conversion;
- `Runtime.lean` for `RuntimeHost`, structured traps, and host functions;
- a `HostEnv` builder aligned positionally with module imports;
- explicit arity and ABI-kind checks at every host boundary; and
- abstract `HostContract`s for the first runtime operations.

Definition of done:

- every generated import has exactly one matching host resolver;
- bad handles and arguments trap with a structured source or target fault;
- concrete hosts satisfy their abstract contracts; and
- literal, constructor, projection, and tag operations execute independently.

### W3: build the differential harness

Provide one entrypoint that runs both semantics:

```lean
runDifferential :
  ImpureProgram -> Name -> Array Impure.Value -> DifferentialResult
```

It should:

1. run the FIR interpreter;
2. lower and validate the program;
3. adapt it to Talos;
4. encode entry arguments and construct the host environment;
5. execute the Talos function;
6. decode the result and host state; and
7. compare outcome, world, external trace, and reachable heap.

The W3 semantic host reuses FIR's deterministic allocator from the same empty
runtime, so the executable comparison intentionally requires equal reachable
locations. Tagged, scalar, and erased entry arguments are supported;
heap-backed arguments are rejected until the harness accepts an explicit
initial runtime. The W4 theorem states the more general address-renaming
relation.

Define a target observation that distinguishes:

- a decoded return value;
- a structured source runtime fault;
- an unexpected target trap;
- invalid Wasm; and
- runner fuel exhaustion.

Only the first two correspond to source observations. Invalid Wasm,
unresolved imports, unexpected traps, and target fuel exhaustion are backend
or harness failures for a terminating supported source execution.

First corpus:

- `abiLiteralProgram`;
- `abiCtorProjectionProgram`;
- `abiCaseProgram`; and
- `abiDefaultCaseProgram`.

These are the final-impure-ABI-correct equivalents of `literalProgram`,
`ctorProjectionProgram`, `caseProgram`, and `defaultCaseProgram`. The original
hand-built fixtures bind possibly tagged `Nat` values as heap-only `object`;
the harness records their rejection under
`FIR-BUG-wasm-none-object-nat-fixture` instead of weakening the proof
fragment.

Definition of done:

- all four ABI-correct programs produce related returns and reachable heaps;
- the harness prints enough evidence to reproduce a mismatch; and
- every possible discrepancy is routed to a Wasm bug card before a workaround.

### W4: prove the first lowering theorem

Use Talos's existing `HostSpec`, `HostEnv.Satisfies`, `wp`,
`TerminatesWith`, and `PartiallyMeets` interfaces.

Proof layers:

1. ABI encode/decode lemmas;
2. concrete runtime hosts satisfy relational contracts;
3. adapter conversion preserves locals, labels, calls, and signatures;
4. lowering preserves the call-free literal/constructor/projection/case
   fragment; and
5. the local result lifts to exported functions and program observations.

Layers 1--3 and the fuel-free executable-to-observation bridge are checked in
`FirTalos/Correctness/`. Layer 4 now covers lowering and host steps for the
whole initial fragment, provides their common instruction-level host-call
lifting, instantiates constructor/projection stack shapes, and proves one
complete source-related constructor-case test. Its active proof obligation is
recursive composition over straight-line code and the case chain; layer 5 can
then instantiate the bridge without mentioning runner fuel in the public
theorem.

The initial theorem excludes closures, external declarations, recursion,
ownership operations, and initialization. These exclusions must appear in an
executable supported-fragment predicate, not remain comments.

A suitable theorem shape is:

```text
source evaluation terminates with observation O
  -> generated Talos execution TerminatesWith observation W
  -> source/target observations are related
```

For programs whose termination is not yet proved, use `PartiallyMeets` rather
than exposing raw fuel in public statements.

### W5: expand the semantic backend

Add vertical slices in this order:

1. `usize` and scalar projections;
2. boxing, unboxing, and `isShared`;
3. object, scalar, and `usize` mutation plus `setTag`;
4. `inc`, `dec`, and deletion;
5. reset and reuse;
6. external calls with world and trace;
7. initialization and global caching; and
8. closures, indirect dispatch, and recursion.

Each slice includes runtime functions, contracts, differential examples, and
an extension of the supported-fragment theorem. Do not mark ownership or
reuse complete using an observational no-op runtime.

### A0: emit the first host-backed Wasm artifact

A0 is an independently assignable artifact lane. It can run in parallel with
W4 because it consumes the checked output of `Fir.Wasm.lower` and the W2 host
contracts without changing either one. Its first result is intentionally a
demonstrator for the initial semantic fragment, not the W6 production runtime.

Deliverables:

1. serialize the validated symbolic instruction subset to standard WAT or a
   `.wasm` binary, with a deterministic command-line entry point;
2. preserve import module/name pairs, signatures, function indices, and
   exports exactly as checked by FIR and exercised by the Talos adapter;
3. provide an external-engine host shim for the W2 `fir.*` imports using the
   same opaque-handle behavior and structured failure boundary;
4. run the four W3 ABI-correct literal/constructor/projection/case programs in
   that engine; and
5. compare decoded returns and observable runtime state with the existing W3
   differential oracle, recording every discrepancy as a Wasm bug card.

Lane boundary and ownership:

- prefer new emitter modules under `Fir/Wasm/Emit/` and isolated runner/tests
  under `integration/talos/artifact/`;
- do not edit `Fir/Wasm/ABI.lean`, `Fir/Wasm/Lower.lean`,
  `Fir/Wasm/WellFormed.lean`, or `FirTalos/Correctness/` in the A0 branch;
- do not add a second ABI, locally reinterpret handles, or silently accept a
  program rejected by `lowerSupported` or `validateModule`;
- route any required root build-target or shared-contract change through the
  integration owner as a separate commit; and
- report the chosen external engine and encoder, including their pinned
  versions and licensing consequences, before making them required tooling.

Definition of done:

- one deterministic command produces an artifact from every program in the
  initial W3 corpus;
- an independent standards-conforming engine validates and executes it;
- the four decoded outcomes agree with W3, including reachable heap evidence;
- malformed or unsupported modules fail before emission with specific errors;
- emitted artifacts are reproducible byte-for-byte (or text-for-text for the
  initial WAT checkpoint); and
- `git diff --check`, `make check`, `make talos-check`, and the lane-local
  external-engine tests pass.

A0 hands back an emitter API over a validated `Fir.Wasm.Module`, an artifact
CLI, the isolated host shim, and engine-level regression evidence. W4 may use
that evidence as testing support, but no W4 theorem depends on the external
engine or serializer.

### W6: refine to a concrete runtime

Once the semantic backend is stable, introduce a separate concrete target:

- choose wasm32 or wasm64 and fix pointer-width semantics;
- specify tagged values and heap layout in linear memory;
- implement allocation, fields, closures, and reference counts;
- relate concrete addresses to FIR locations and semantic handles;
- prove each concrete runtime operation refines its W2 contract; and
- compose that refinement with the lowering theorem.

Binary encoding and production ABI compatibility begin here, not in W0.

## Parallel agent packages

After W0 lands, use file-level ownership to minimize conflicts:

| Package | Primary files | Dependencies |
|---|---|---|
| ABI and validation | `Fir/Wasm/ABI.lean`, `Fir/Wasm/WellFormed.lean` | W0 gate |
| Symbolic lowering | `Fir/Wasm/Lower.lean`, lowering fixtures | frozen ABI |
| Talos adapter | `FirTalos/Adapter.lean`, adapter fixtures | frozen ABI |
| Host codec/runtime | new `FirTalos/Codec.lean`, `Runtime.lean` | frozen ABI |
| Contracts/proofs | new `FirTalos/Contracts.lean`, `Correctness/` | codec and adapter APIs |
| Differential tests | new `FirTalos/Differential.lean` | adapter and runtime |
| A0 artifact emission | new `Fir/Wasm/Emit/`, `integration/talos/artifact/` | W1 checker, W2 contracts, W3 corpus |

Only one package owns an existing shared file at a time. Prefer new modules
for contracts, fixtures, and proofs. If an agent discovers that the frozen ABI
must change, stop dependent work and route a standalone contract commit
through integration rather than letting branches drift.

## First milestone

The first milestone is complete when:

- W0 ABI kinds and encoding rules are frozen;
- the symbolic module passes FIR validation;
- the four constructor/case programs execute in Talos;
- returned values, runtime world/trace, and reachable heaps match FIR;
- the concrete host functions satisfy abstract Talos host contracts;
- a checked theorem covers the restricted call-free fragment;
- `git diff --check`, `make check`, and `make talos-check` pass; and
- all discovered discrepancies have bug-card IDs.

## Integration and handoff

Commit small green vertical slices. Rebase on local `main` after every shared
contract lands and before handoff; never merge `main` into this branch.

Each handoff reports:

- base and head commits;
- completed W-stage slice;
- files and shared contracts changed;
- exact checks and results;
- Wasm bug-card IDs, or `none`; and
- known follow-ups.

The worktree must be clean at handoff.
