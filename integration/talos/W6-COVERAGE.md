# W6 concrete-runtime coverage matrix

This is the operation-level audit companion to `PLAN.md`. “Heap theorem”
means a successful operation is related through `LiveHeapRel` or
`ConcreteRuntimeRel`; it does not imply W2 lowering composition or complete
failure correspondence. The matrix is intentionally conservative.

| `RuntimeOp` | Concrete executable | Successful refinement | Structured failures | W6.6 composition/artifact |
|---|---|---|---|---|
| `literal` | Naturals only | Tagged encoder and large-natural heap theorem | Partial | Missing; strings missing |
| `allocCtor` | Yes | Nonempty heap and tagged empty theorems | Partial | Missing |
| `objectProj` | Yes | Heap theorem | Partial | Missing |
| `usizeProj` | Yes | Heap theorem | Partial | Missing |
| `scalarProj` | Four integer widths | Heap theorems | Partial | Missing; floats tracked by `FIR-BUG-wasm-none-float-runtime-gap` |
| `cacheSet` | Typed concrete globals | Runtime theorem | Partial | Missing |
| `partialApply` | Closure allocation | Heap theorem | Partial | Missing |
| `closureApply` | Metadata exists; no concrete dispatch step | Missing | Missing | Missing |
| `closureMatches` | Yes | Exact match/nonmatch heap theorem | Partial | Missing |
| `closureProj` | Yes | Typed heap theorem | Partial | Missing |
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
| `getTag` | Yes | Complete `.tobject` constructor/tagged theorem | Partial | Missing |

Cross-cutting W6.5 state:

- globals, world, trace, successful external calls, and failed external calls
  have `ConcreteRuntimeRel`/trap boundaries;
- `ConcreteError.toTrap` preserves source-vs-target classification and maps
  address-bearing underflow back to semantic locations;
- the full per-operation failure matrix is not yet proved; and
- no concrete operation is yet composed with the W5/W2 lowering theorem, and
  the generated V8 artifact lane still uses the semantic host runtime.

Update this table in the same commit whenever an operation crosses one of
these boundaries. A broad W6 completion claim requires every supported row to
be green through the final column, with exclusions tied to an explicit bug
card or documented fragment gate.
