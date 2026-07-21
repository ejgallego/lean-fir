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
| `cacheSet` | Typed concrete globals and Talos host | Runtime theorem | Partial | Concrete host-call and generated cache-write suffix WP; interprocedural lazy-`let` and artifact pending |
| `partialApply` | Concrete Talos closure allocation | Heap theorem | Partial | Source interpreter, compiler/adapter, arbitrary-arity host call/local write, and continuation compose; artifact pending; `.tagged` result gap tracked by `FIR-BUG-wasm-none-partial-apply-tagged-result` |
| `closureApply` | Legacy callback excluded; generated trampoline uses metadata, capture projection, and direct calls | Not applicable as a runtime operation | Not applicable as a runtime operation | Concrete interprocedural judgment plus candidate and fuel-free direct-call/local-write rules; complete compiler fold/callee proof and artifact pending |
| `closureMatches` | Concrete Talos metadata host | Exact match/nonmatch heap theorem | Partial | Generated matcher plus one candidate `if`/fallthrough WP; complete compiler candidate fold, direct call, and artifact pending |
| `closureProj` | Concrete Talos typed-capture host | Typed heap theorem | Partial | Generated `local.get; closureProj` capture-stack WP; full trampoline/direct-call and artifact pending |
| `reset` | Yes | Tagged, nonunique, and unique protocol theorems | Partial | Missing |
| `reuse` | Yes | Fresh empty/nonempty and in-place theorems | Partial | Missing |
| `box` | Five integer/USize kinds | Tagged and heap theorems | Partial | Missing; floats share the runtime gap |
| `unbox` | Five integer/USize kinds | Tagged and heap theorems | Partial | Missing; floats share the runtime gap |
| `isShared` | Yes | Tagged and ordinary heap theorem | Partial | Missing |
| `objectSet` | Yes | Heap theorem | Partial | Missing |
| `usizeSet` | Yes | Heap theorem | Partial | Missing |
| `scalarSet` | Four integer widths | Heap theorems | Partial | Missing; floats share the runtime gap |
| `setTag` | Yes | Heap theorem | Partial | Missing |
| `inc` | Yes | Ordinary heap theorem; exact tagged equation | Partial | Missing |
| `dec` | Yes | Complete checked recursive heap theorem | Partial | Missing |
| `delete` | Yes | Ordinary heap and erased-sentinel theorems | Partial | Missing |
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
- the other supported operations still need that composition, while the
  generated V8 artifact lane continues to use the semantic host runtime.

Update this table in the same commit whenever an operation crosses one of
these boundaries. A broad W6 completion claim requires every supported row to
be green through the final column, with exclusions tied to an explicit bug
card or documented fragment gate.
