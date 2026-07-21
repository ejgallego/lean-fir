# W6 concrete-runtime coverage matrix

This is the operation-level audit companion to `PLAN.md`. “Heap theorem”
means a successful operation is related through `LiveHeapRel` or
`ConcreteRuntimeRel`; it does not imply W2 lowering composition or complete
failure correspondence. The matrix is intentionally conservative.

| `RuntimeOp` | Concrete executable | Successful refinement | Structured failures | W6.6 composition/artifact |
|---|---|---|---|---|
| `literal` | Naturals only | Tagged encoder and large-natural heap theorem | Partial | Natural concrete host plus generated literal-`let` WP; artifact pending; strings missing |
| `allocCtor` | Yes | Nonempty heap and tagged empty theorems | Partial | Concrete Talos host plus arbitrary-arity generated constructor-`let` WP; artifact pending |
| `objectProj` | Yes | Heap theorem | Partial | Concrete Talos host plus generated projection-`let` WP; artifact pending |
| `usizeProj` | Yes | Heap theorem | Partial | Concrete Talos host plus generated projection-`let` WP; artifact pending |
| `scalarProj` | Four integer widths | Heap theorems | Partial | Integer concrete host plus generated projection-`let` WP; artifact pending; floats tracked by `FIR-BUG-wasm-none-float-runtime-gap` |
| `cacheSet` | Typed concrete globals, recursive graph persistence, and Talos host | Constructive for all non-heap lanes and ordinary boxed/natural leaf roots; constructor recursive-step theorem proved; explicit `CachePersistenceRefines` remains for complete recursive graphs | Partial | Concrete hit/miss control, witness-indexed source/compiler judgment, terminating declaration call, host call, both global writes, cached-value reload, and local write compose; closure filtering/global fuel induction, per-declaration body proofs, and artifact switch pending |
| `partialApply` | Concrete Talos closure allocation | Heap theorem | Partial | Source interpreter, compiler/adapter, arbitrary-arity host call/local write, and continuation compose; artifact pending; `.tagged` result gap tracked by `FIR-BUG-wasm-none-partial-apply-tagged-result` |
| `closureApply` | Legacy callback excluded; generated trampoline uses metadata, capture projection, and direct calls | Not applicable as a runtime operation | Not applicable as a runtime operation | Concrete interprocedural judgment, body-WP-to-termination bridge, candidate and direct-call/local-write rules; complete compiler fold and artifact pending |
| `closureMatches` | Concrete Talos metadata host | Exact match/nonmatch heap theorem | Partial | Generated matcher plus one candidate `if`/fallthrough WP; complete compiler candidate fold, direct call, and artifact pending |
| `closureProj` | Concrete Talos typed-capture host | Typed heap theorem | Partial | Generated `local.get; closureProj` capture-stack WP; full trampoline/direct-call and artifact pending |
| `reset` | Yes | Tagged, nonunique, and unique protocol theorems | Partial | Concrete Talos host plus tagged/fallback/unique source/compiler/adapter composition, exact unary call, reuse-token local write, and arbitrary continuation; artifact pending |
| `reuse` | Yes | Fresh empty/nonempty and in-place theorems | Partial | Concrete Talos host plus all three source/compiler/adapter branches, arbitrary-arity token/field call, descriptor transport, result-local write, and arbitrary continuation; artifact pending |
| `box` | Five integer/USize kinds | Tagged and heap theorems | Partial | Witness-growing concrete host, source/compiler/adapter composition, exact unary call and object local write, and arbitrary continuation compose; floats share the runtime gap; artifact pending |
| `unbox` | Five integer/USize kinds | Tagged and heap theorems | Partial | ABI-indexed concrete host, representation-indexed source step, compiler/adapter, generated unary result call, exact i32/i64 local write, and continuation compose; heap descriptor/result-kind match stays explicit; floats share the runtime gap; artifact pending |
| `isShared` | Yes | Immediate, promoted, and ordinary heap theorem | Partial | Concrete object-like host, source step, compiler/adapter, generated unary result call, direct UInt8 local write, and continuation compose; artifact pending |
| `objectSet` | Yes | Heap theorem | Partial | Concrete two-i32 host, FVar source step, compiler/adapter, generated binary call, and continuation compose for supported object-field kinds; artifact and non-FVar arguments pending |
| `usizeSet` | Yes | Heap theorem | Partial | Concrete i32/i64 host, source step, compiler/adapter, generated binary call, and continuation compose; artifact pending |
| `scalarSet` | Four integer widths | Heap theorems | Partial | Concrete width dispatcher, FVar source step, compiler/adapter, generated binary call, and continuation compose for initially empty semantic packed fields; repeated/disjoint field frame pending; floats share the runtime gap; artifact pending |
| `setTag` | Yes | Heap theorem | Partial | Concrete header host, source step, compiler/adapter, generated unary call, and continuation compose; explicit wasm32 tag-fit premise retained; artifact pending |
| `inc` | Yes | Ordinary heap theorem; exact tagged equation | Partial | Concrete ordinary/tagged/promoted host, source step, compiler/adapter, generated unary call, persistent elision, and continuation compose; ordinary wasm32 count-fit premise retained; artifact pending |
| `dec` | Yes | Complete checked recursive heap theorem | Partial | Concrete checked ordinary/tagged/promoted recursive host, source step, compiler/adapter, generated unary call, persistent elision, and continuation compose with explicit closure-descriptor identity; unchecked nonpersistent composition and artifact pending |
| `delete` | Yes | Ordinary heap and erased-sentinel theorems | Partial | Concrete canonical-delete/erased-zero host, representation-indexed source step, compiler/adapter, generated unary call, and continuation compose without weakening ordinary object decoding; artifact pending |
| `getTag` | Yes | Complete `.tobject` constructor/tagged theorem | Partial | Concrete Talos host plus generated constructor-case WP; artifact pending |

Cross-cutting W6.5 state:

- globals, world, trace, successful external calls, and failed external calls
  have `ConcreteRuntimeRel`/trap boundaries;
- `ConcreteError.toTrap` preserves source-vs-target classification and maps
  address-bearing underflow back to semantic locations;
- the full per-operation failure matrix is not yet proved; and
- natural literals, `allocCtor`, `partialApply`, `getTag`, `objectProj`,
  `usizeProj`, and all four supported integer `scalarProj` variants are
  composed with their W5/W2 generated case and `let` theorems using
  representation-aware concrete locals and host-owned memory; and
- lazy-cache hits and misses compose through the declaration-call termination
  boundary, typed host cache update, physical flag/value globals, and generated
  result-local write; scalar, erased/reuse, direct-tag, promoted-tag, and
  ordinary boxed/natural leaf roots discharge cache persistence constructively;
  ordered ownership folds and one recursive constructor step are proved, while
  closure filtering and the global fuel induction keep the explicit proof
  premise rather than the former heap-unchanged assumption; and
- reference-count increment composes through exact object-like local widening,
  the concrete header/tagged operation, generated no-result host call, and
  persistent compiler elision; and
- checked reference-count decrement composes through exact object-like local
  widening, the complete recursive ownership theorem, generated no-result host
  call, and persistent compiler elision; closure descriptor identity remains
  explicit and unchecked nonpersistent composition remains open; and
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
  artifact execution remains pending; and
- reuse composes through fresh tagged, fresh heap, and in-place protocol
  branches, transporting the exact constructor descriptor across the generated
  token-plus-fields host call, result-local write, and continuation; artifact
  execution remains pending; and
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
  i32/i64 lanes and generated binary host calls for the initial-empty-field
  theorem fragment; repeated/disjoint scalar framing remains open; and
- the other supported operations still need that composition, while the
  generated V8 artifact lane continues to use the semantic host runtime.

Update this table in the same commit whenever an operation crosses one of
these boundaries. A broad W6 completion claim requires every supported row to
be green through the final column, with exclusions tied to an explicit bug
card or documented fragment gate.
