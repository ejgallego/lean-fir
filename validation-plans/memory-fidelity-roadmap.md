# Memory-fidelity validation roadmap

This roadmap narrows the validation lane's near-term priority to Lean's logical
memory lifecycle while preserving the broader interpreter-validation goal.
Lean native execution remains the semantic oracle, final LCNF provides the
compiler-path ownership witness, the LCNF interpreter provides exact dynamic
execution evidence, and compiler-generated Wasm runs in a real engine when the
corresponding W7 surface is linked.

The roadmap validates logical allocation, ownership, and release. It does not
compare physical allocator addresses or require native, LCNF, and Wasm to use
the same heap layout.

## Progress

| Milestone | State | Current checkpoint | Next acceptance step |
| --- | --- | --- | --- |
| M0 Mixed closure baseline | prepared | `mixed-closure-capture-once` and `mixed-closure-capture-twice` pin 36 and 62 interpreter transitions and pass the native/LCNF/V8 triangle | Land the fixture-only admission on `main` |
| M1 Ownership coverage ledger | active | Existing coverage distinguishes unique/shared, copy-on-write, recursive release, and closure multiplicity | Add lifetime-operation, alias-shape, and observation-strength domains with each fixture slice |
| M2 Closure/capture ownership | active | One-use/two-use mixed captures and the outside-alias ByteArray read/mutate pair are prepared | Cover zero/three uses and unique/shared final application |
| M3 Allocation and reuse | queued | Constructor, String, ByteArray, reset/reuse, growth, and copy-on-write fixtures already provide a base | Add paired reuse-versus-fresh-allocation cases across heap kinds and retained capacities |
| M4 Recursive release | queued | Direct LCNF covers repeated aliases, nested release, shared stopping, and persistent owners | Add source-generated observable release pairs and exact decrement multiplicities |
| M5 Nonlocal control | queued | External yield/bind and ordered effects are observable | Carry owned aliases across an external suspension; add caught exceptions only after their shared protocol lands |
| M6 Real-engine promotion | continuous | Scalar closures and the mixed one-use/two-use pair run through native/LCNF/V8 | Promote at least one representative pair per ownership domain whenever W7 support is linked |

States are `queued`, `active`, `prepared`, `landed`, or `parked`. A prepared
slice is committed and locally validated but still waits at a named cross-lane
boundary. A milestone becomes landed only after its fixture commit is on
`main` and every eligible case has passed its required backend triangle.

## Coverage model

Use the existing case tags and conjunctive coverage domains to cover a compact
cross-product of these axes. Do not construct the full Cartesian product.

- Lifetime operation: allocate, retain, release, reuse, and persist.
- Owner state: unique, shared, and persistent.
- Alias graph: one owner, an independently retained alias, the same child in
  multiple fields or captures, a nested chain, and a shared DAG.
- Consumer behavior: ignore/drop, borrow/read, return/transfer, and
  consume/mutate.
- Boundary: closure application, constructor reset/reuse, external
  yield/effect, return, and eventually caught exception.
- Heap kind: constructor, String, ByteArray, large Nat/Int, and floating box.
- Observation: surviving-alias contents, copy-on-write, returned aliases,
  ordered effects, exact ownership facts, exact dynamic form counts, and exact
  execution traces.

Prefer pairs in which one program takes an ownership-sensitive path and the
other avoids it. Use pairwise coverage to vary one or two axes at a time, and
add a coverage requirement for the distinguishing conjunction.

## Per-fixture acceptance

Every memory-fidelity fixture must satisfy the applicable requirements below.

1. Native Lean supplies the result, ordered effects, failure, and output
   observation. No expected semantic result is substituted for the oracle.
2. The source and dependency list are small enough that the targeted ownership
   path is identifiable in final LCNF.
3. Required final-LCNF forms prove the compiler retained the intended path.
4. Exact executed form traces and exact multiplicities prove the interpreter
   executed the allocation, `pap`/closure invocation, increment, decrement,
   projection, mutation, reuse, or release operations being claimed.
5. The returned value or ordered effect makes an ownership mistake observable.
   Copy-on-write and retained aliases are preferred over internal-state-only
   assertions.
6. Native ownership attestations are added when compiler-generated ownership
   facts, rather than only semantic behavior, form part of the claim.
7. The case runs in V8 after the W7 compiler surface and W6 contract for that
   feature are linked. Until then it carries the existing explicit pending
   fence and does not inflate V8 coverage.
8. Any semantic discrepancy receives a bug card before a workaround or model
   accommodation is introduced.

## Planned fixture slices

### S1: outside-alias ByteArray capture

State: `prepared` on `validation/closure-ownership-fixtures`.

Pair a closure that borrows a captured ByteArray with a closure that consumes
and mutates it through `ByteArray.set!`. Both retain the original ByteArray
outside the closure. The mutation case must therefore allocate a copy and
return both the unchanged outside alias and the updated result. Pin `pap`,
closure invocation, capture projection, increment/decrement, external dispatch,
constructor return, and exact ordered traces.

This slice uses the existing ByteArray protocol and does not depend on argument
alias materialization or the effect-wrapper contracts.

### S2: closure-use multiplicity

Extend the same-closure matrix to zero, one, two, and three uses. Keep the
zero-use case only if final LCNF retains a real closure allocation; otherwise
cover that machine state in the direct-LCNF tier. Distinguish a shared
intermediate application from a unique final application with exact increment
and decrement counts.

### S3: capture alias topology

Compare one captured heap object with the same object captured in multiple
slots, then retain an independent alias outside the closure. Cover callees that
ignore, read, return, and consume/mutate the capture. Use constructor, String,
ByteArray, large Nat/Int, and floating boxes as pairwise representatives rather
than repeating a scalar matrix.

### S4: recursive release and reuse

Cover repeated child aliases, nested unique release, shared-child recursion
stopping, persistent owners, erased/scalar neighbors, same-size reuse, retained
capacity, and grow/delete/allocation. Make release order observable through a
surviving alias, later copy-on-write, or a reuse decision, and pin exact
`project-dec`, `dec`, `reset`, `reuse`, `del`, `oset`, and `setTag` counts.

### S5: nonlocal ownership boundaries

Apply a closure, cross an external suspension or ordered effect, then reuse a
different alias. Admit the captured aliased-ByteArray taken/skipped pair only
after argument-alias materialization and the boxed effect protocol are linked.
Add caught exceptions after the source-entry/error contract is accepted by all
participating backends.

## Lane boundaries

The validation lane owns source fixtures, validation projections, exact traces,
coverage requirements, evidence, validation documentation, and discrepancy
cards. It does not modify shared interpreter semantics, pass proofs, the W6
concrete heap/runtime or its refinement, or W7 generation and artifact
adapters. A fixture that exposes a missing shared contract is parked behind a
coordination handoff rather than locally weakening or duplicating that
contract.
