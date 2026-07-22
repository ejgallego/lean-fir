# W6 concrete-runtime coverage matrix

This is the operation-level audit companion to `PLAN.md`. “Heap theorem”
means a successful operation is related through `LiveHeapRel` or
`ConcreteRuntimeRel`; it does not imply W2 lowering composition or complete
failure correspondence. The matrix is intentionally conservative.

| `RuntimeOp` | Concrete executable | Successful refinement | Structured failures | W6.6 composition/artifact |
|---|---|---|---|---|
| `literal` | Naturals and UTF-8 strings | Tagged encoder, large-natural heap theorem, and fresh-string `LiveHeapRel` theorem with exact UTF-8 object decoding | Partial | Natural and string concrete hosts plus generated literal-`let` WPs and compiler-local writes; string whole-module Talos/Node/browser execution |
| `allocCtor` | Yes | Nonempty heap and tagged empty theorems | Partial; invalid-arity classification blocked by `FIR-BUG-wasm-none-constructor-arity-fault-classification` | Concrete Talos host plus arbitrary-arity generated constructor-`let` WP, whole-module concrete Talos execution, and Node/V8 plus browser-Worker checked-header execution |
| `objectProj` | Yes | Live and stale mapped-heap theorems | Bounds and dead-object source-address faults exact; remainder partial | Concrete Talos host plus generated projection-`let` WP, exact source-classified bounds and stale-object traps with executable guards, whole-module concrete Talos execution, and successful/failing Node/V8 plus browser-Worker checked-slot execution |
| `usizeProj` | Yes | Live and stale mapped-heap theorems | Bounds and dead-object source-address faults exact; remainder partial | Concrete Talos host plus generated projection-`let` WP, exact source-classified bounds and stale-object traps with executable guards, whole-module concrete Talos execution, and compiler-shaped Node/V8 plus browser-Worker write/read execution |
| `scalarProj` | Four integer widths | Live packed-field and stale mapped-heap theorems | Dead-object source-address fault exact for all four widths; live uninitialized-coordinate correspondence blocked by `FIR-BUG-wasm-none-uninitialized-scalar-projection`; remainder partial | Integer concrete host plus generated projection-`let` WP, a four-width deleted-object trap guard, and compiler-shaped `UInt8`/`UInt16`/`UInt32`/`UInt64` whole-module, Node/V8, and browser-Worker write/read execution; invalid hand fixture retains its exact external-engine failure under `FIR-BUG-wasm-none-scalar-slot-layout-contract`; floats tracked by `FIR-BUG-wasm-none-float-runtime-gap` |
| `cacheSet` | Typed concrete globals, recursive graph persistence, and Talos host | Constructive for every represented non-heap lane and mapped constructor, closure, box, natural, or string graph; public fuel and descriptor-table identity proved | Partial | Concrete hit/miss control, witness-indexed source/compiler judgment, terminating declaration call, host call, both global writes, cached-value reload, local write, twice-called cached constructor-graph whole-module execution, and Node/V8 plus browser-Worker miss/persistence/hit execution compose; per-declaration body proofs pending; canonical dead-child gap fixed by `FIR-BUG-wasm-none-persistence-dead-child-refinement` |
| `partialApply` | Concrete Talos closure allocation | Heap theorem | Partial | Source interpreter, compiler/adapter, arbitrary-arity host call/local write, continuation, module-derived metadata tables, ordinary/erased/multi-stage whole-module executions, and Node/V8 plus browser-Worker concrete closure allocation compose; `.tagged` result gap tracked by `FIR-BUG-wasm-none-partial-apply-tagged-result` |
| `closureApply` | Legacy callback excluded; generated trampoline uses metadata, capture projection, and direct calls | Not applicable as a runtime operation | Not applicable as a runtime operation | Concrete interprocedural judgment, body-WP-to-termination bridge, candidate and direct-call/local-write rules, plus ordinary/erased/multi-stage whole-module Node/V8 and browser-Worker executions; complete compiler candidate-fold proof pending |
| `closureMatches` | Concrete Talos metadata host | Exact match/nonmatch heap theorem | Partial | Generated matcher plus one candidate `if`/fallthrough WP, module-derived dispatch table, and ordinary/erased/multi-stage whole-module Node/V8 and browser-Worker executions; complete compiler candidate-fold proof pending |
| `closureProj` | Concrete Talos typed-capture host | Typed heap theorem | Partial | Generated `local.get; closureProj` capture-stack WP, module-derived descriptor table, and ordinary/multi-stage whole-module Node/V8 and browser-Worker executions; erased captures correctly skip projection; complete compiler candidate-fold proof pending |
| `reset` | Yes | Tagged, nonunique, and unique protocol theorems | Partial | Concrete Talos host plus tagged/fallback/unique source/compiler/adapter composition, exact unary call, reuse-token local write, arbitrary continuation, unique/nonunique whole-module executions, and unique/shared Node/V8 plus browser-Worker concrete execution |
| `reuse` | Yes | Fresh empty/nonempty and in-place theorems | Partial | Concrete Talos host plus all three source/compiler/adapter branches, arbitrary-arity token/field call, descriptor transport, result-local write, arbitrary continuation, in-place/fresh whole-module executions, and in-place/fresh Node/V8 plus browser-Worker concrete execution |
| `box` | Five integer/USize kinds | Tagged and heap theorems | Partial | Witness-growing concrete host, source/compiler/adapter composition, exact unary call, object local write, maximum-`UInt64` whole-module execution, and Node/V8 plus browser-Worker heap-box/round-trip execution compose; floats share the runtime gap |
| `unbox` | Five integer/USize kinds | Tagged and heap theorems | Partial | ABI-indexed concrete host, representation-indexed source step, compiler/adapter, generated unary result call, exact i32/i64 local write, continuation, maximum-`UInt64` whole-module execution, and Node/V8 plus browser-Worker heap-box/round-trip execution compose; heap descriptor/result-kind match stays explicit; floats share the runtime gap |
| `isShared` | Yes | Immediate, promoted, ordinary live-heap, and stale mapped-heap theorems | Dead-object source-address fault exact through `LiveHeapRel`, `ConcreteErrorSourceRel`, and the Talos host; remainder partial | Concrete object-like host, source step, compiler/adapter, generated unary result call, direct UInt8 local write, continuation, tagged/unique whole-module executions, and ordinary-object Node/V8 plus browser-Worker execution compose; the deleted-object guard and proof close `FIR-BUG-wasm-none-dead-object-fault-classification` |
| `objectSet` | Yes | Live and stale mapped-heap theorems | Bounds and dead-object source-address faults exact with no post-state; remainder partial | Concrete two-i32 host, exact source-classified bounds and stale-object traps/no-write guards, FVar and erased-constant source steps, compiler/adapter, generated binary or local/constant call, continuation, whole-module mutation/readback including canonical erased zero, and Node/V8 plus browser-Worker checked-slot execution compose for every `LCNF.Arg` form and supported object-field kind |
| `usizeSet` | Yes | Live and stale mapped-heap theorems | Bounds and dead-object source-address faults exact with no post-state; remainder partial | Concrete i32/i64 host, exact source-classified bounds and stale-object traps/no-write guards, source step, compiler/adapter, generated binary call, continuation, whole-module write, and compiler-shaped Node/V8 plus browser-Worker write/read execution compose |
| `scalarSet` | Four integer widths | Live and stale mapped-heap theorems, including same-coordinate replacement and disjoint retained-field framing for every integer width | Dead-object source-address fault exact for all four widths with no post-state; remainder partial | Concrete width dispatcher, FVar source step, compiler/adapter, generated binary call, continuation, and compiler-shaped `UInt8`/`UInt16`/`UInt32`/`UInt64` whole-module, Node/V8, and browser-Worker write/readback compose; repeated same-coordinate writes refine the source replacement filter and execute twice in one module; disjoint two-coordinate Talos modules for all four widths preserve the first coordinate after the second write; the four-width deleted-object guard checks exact traps and byte preservation; invalid hand fixture retains its exact external-engine failure under `FIR-BUG-wasm-none-scalar-slot-layout-contract`; floats share the runtime gap |
| `setTag` | Yes | Live and stale mapped-heap theorems | Dead-object source-address fault exact with no post-state; remainder partial | Concrete header host, exact stale-object trap/no-write guard, source step, compiler/adapter, generated unary call, continuation, whole-module case/readback, and Node/V8 plus browser-Worker header mutation compose; explicit wasm32 tag-fit premise retained |
| `inc` | Yes | Ordinary, tagged, and stale mapped-heap theorems | Dead-object source-address fault exact with no post-state; remainder partial | Concrete ordinary/tagged/promoted host, exact stale-object trap/no-write guard, source step, compiler/adapter, generated unary call, persistent elision, continuation, shared-reset whole-module execution, and balanced/shared-reset Node/V8 plus browser-Worker execution compose; ordinary wasm32 count-fit premise retained |
| `dec` | Yes | Complete recursive heap theorem for either outer check bit plus stale mapped-heap theorem for every positive amount | Positive-count dead-object source-address fault exact with no post-state; zero count is the specified empty-fold no-op; remainder partial | Concrete checked/unchecked ordinary recursive host, checked tagged/promoted no-op, exact stale-object trap/no-write guard, source step, compiler/adapter, generated unary call, persistent elision, continuation, checked and unchecked constructor-graph whole-module release, and balanced/recursive Node/V8 plus browser-Worker ownership executions compose with explicit closure-descriptor identity |
| `delete` | Yes | Ordinary heap and erased-sentinel theorems | Partial | Concrete canonical-delete/erased-zero host, representation-indexed source step, compiler/adapter, generated unary call, continuation, ordinary-object whole-module deletion, and exact dead-object Node/V8 plus browser-Worker execution compose without weakening ordinary object decoding |
| `getTag` | Yes | Complete `.tobject` constructor/tagged success theorem plus mapped stale-heap theorem | Dead-object source-address fault exact through `LiveHeapRel`, `ConcreteErrorSourceRel`, and the Talos host; remainder partial | Concrete Talos host plus generated constructor-case WP, whole-module concrete Talos execution, a direct allocate/delete/tag trap guard, and Node/V8 plus browser-Worker constructor-case execution |

Cross-cutting W6.5 state:

- the frozen UTF-8 string writer has exact byte readback and spatial-frame
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
- `ConcreteError.toTrap` preserves source-vs-target classification and maps
  address-bearing dead-object and underflow faults back to semantic locations;
- mapped live-constructor object and `USize` projections preserve an exact
  semantic bounds fault through the checked reader, complete runtime relation,
  and Talos source-classified trap, including the original index and declared
  size;
- the matching object and `USize` setters preserve those exact source faults
  before either concrete or semantic state changes, and executable Talos guards
  reread the original payload after each trap;
- stale mapped references now use a source-address `deadObject address` trap;
  reusable `DeadCellRel` and `LiveHeapRel` lemmas plus the `isShared`, `getTag`,
  object-, `USize`-, and four-width scalar-projection Talos theorems preserve it
  against FIR's `deadObject location`, with `HeapReferenceRel` carrying the
  exact fault translation; stale object-, `USize`-, tag-, and four-width
  scalar-mutation and ownership theorems add the same no-post-state boundary
  (for positive-count `dec`; zero remains an empty fold); closed sharing and direct
  tag/projection/mutation guards cover execution, while the fixed
  classification is tracked by
  `FIR-BUG-wasm-none-dead-object-fault-classification`;
- invalid constructor arities are `malformed` in FIR but dedicated source
  `arityMismatch` faults in the concrete allocator; exact guards and the
  coordinated contract decision are tracked by
  `FIR-BUG-wasm-none-constructor-arity-fault-classification`;
- the full per-operation failure matrix is not yet proved; and
- natural and string literals, `allocCtor`, `partialApply`, `getTag`, `objectProj`,
  `usizeProj`, and all four supported integer `scalarProj` variants are
  composed with their W5/W2 generated case and `let` theorems using
  representation-aware concrete locals and host-owned memory; and
- lazy-cache hits and misses compose through the declaration-call termination
  boundary, typed host cache update, physical flag/value globals, and generated
  result-local write; scalar, erased/reuse, direct-tag, promoted-tag, and
  ordinary boxed/natural/string leaf roots discharge cache persistence constructively;
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
  generated unary host call, destination-local write, and continuation; and
- all five supported integer/`USize` box variants compose through their exact
  source scalar and i32/i64 operand lanes, representation-dependent witness
  growth, the generated unary host call, object destination-local write, and
  continuation; and
- reset composes through its immediate, nonunique decrement, and unique
  protocol branches, transporting the representation witness and exact
  reuse-token local through the generated unary host call and continuation;
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
- the remaining supported subfamilies still need whole-module or concrete
  external-engine coverage, while the wider generated Node/browser corpus
  continues to use the semantic JavaScript host runtime in parallel.

Update this table in the same commit whenever an operation crosses one of
these boundaries. A broad W6 completion claim requires every supported row to
be green through the final column, with exclusions tied to an explicit bug
card or documented fragment gate.
