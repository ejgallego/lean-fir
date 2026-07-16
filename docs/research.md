# FIR research notes

This document records architectural rationale. Implementation status and the
ordered work queue live only in `docs/pass-correctness-plan.md`.

## Compiler target

FIR targets `Lean.Compiler.LCNF` in Lean 4.32.0. The normal compiler starts
with base LCNF, lowers it to monomorphic LCNF, lowers that to impure LCNF, and
emits C directly from the final saved impure declarations.

The older `Lean.IR` remains in Lean. Final impure LCNF is also translated
through `Lean.IR.toIR` for interpreter metadata and LLVM-related consumers,
but that is a parallel branch rather than an intermediate representation on
the direct C-emission path. `docs/lcnf-to-c.md` records the exact 4.32 pass
sequence.

Lean exposes three phase-level LCNF representations:

| Phase | Syntax index | Distinguishing property |
|---|---|---|
| base | `.pure` | source type information and polymorphism remain |
| mono | `.pure` | polymorphism has been eliminated |
| impure | `.impure` | runtime layout, mutation, effects, and ownership are explicit |

Because base and mono share the `.pure` syntax index, FIR wraps declarations
in `Program phase`. This prevents statements about the two compiler snapshots
from being mixed accidentally and gives each phase a place for its own
well-formedness invariant.

## Semantic foundation

`Fir.LeanIR.Impure` is the reference semantics for the lower, pre-Wasm
boundary. Its runtime model includes:

- tagged and heap object references, machine scalars, `usize`, erased values,
  and reset/reuse tokens;
- constructor fields split into object, `usize`, and scalar storage;
- closures, boxes, strings, natural values, opaque objects, reference counts,
  persistent objects, and liveness;
- allocation, projections, mutation, tagging, boxing, reference-count
  operations, deletion, reset, and reuse;
- typed external requests and responses, an abstract world, and an observable
  external-event trace.

The canonical semantics is the relational `Step` in
`Fir/LeanIR/Interpreter.lean`. The executable runner uses the same core step
function, and its soundness results produce relational executions. Outcomes
distinguish returned values and runtime faults; running out of fuel belongs to
the runner, not to source-program behavior. The final impure instruction
forms are handled exhaustively, so this semantics has no catch-all
"unmodeled instruction" result.

Observational equivalence for pass proofs is deliberately stronger than
return-value equality and weaker than heap equality. It compares returned
values or faults, the external world and trace, and the heap reachable from
observable roots, modulo a partial address renaming. Unreachable garbage is
not observable.

The original evaluator remains under `Fir.LeanIR.Legacy` as a small,
non-exported differential baseline. `lake lean Inspect` compiles four real
Lean declarations through `LCNF.main`, reads their saved impure LCNF, and
reports both the legacy result and the new machine result. In Lean 4.32 the
new machine executes all four:

| Declaration | Relevant emitted form | New machine |
|---|---|---|
| `litNat` | literal and return | executes |
| `idNat` | borrowed parameter, `inc`, return | executes |
| `branchNat` | constructor `cases` | executes |
| `pairFirst` | object projection and `inc` | executes |

## Pass-proof harness

`Fir.LeanIR.Pipeline` copies the exact built-in 4.32 pass keys, including
occurrence numbers and phase transitions, and checks them against
`LCNF.builtinPassManager` at elaboration time. A Lean upgrade that changes the
pipeline therefore fails locally instead of silently invalidating the proof
roadmap.

The same module constructs the proof worklist mechanically in reverse:
`saveImpure` back through the impure passes, then late mono, SCC splitting,
early mono, base, and finally `toLCNF`. Administrative passes can be discharged
separately from behavior-changing passes. The theorem interfaces are present;
proofs for the individual upstream transformations are the continuing
campaign.

`Fir.LeanIR.Checkpoint` also provides an opt-in wrapper around Lean 4.32's
actual `simpCase` pass. `Inspect` installs it dynamically, records declaration
groups immediately before and after the pass, and reports per-sample size
deltas. The wrapper calls the upstream pass body and is not registered
globally, so importing FIR does not change downstream compilation.

## WebAssembly direction

`Fir.Wasm` defines a small semantic ABI over core Wasm value types. Object
references and most Lean values use `i32`; `UInt64` and `USize` use `i64`.
Every impure LCNF value or instruction form lowers either to core symbolic
Wasm control/data instructions or to a typed `fir.*` runtime operation.
Runtime imports are generated and deduplicated from actual use.

The optional package in `integration/talos` resolves symbolic locals, branch
labels, calls, imports, functions, and exports into Talos's `Wasm.Module`.
It pins a Talos revision whose interpreter uses Lean 4.32. Its smoke test runs
a scalar identity module in Talos. Runtime implementations for heap-bearing
`fir.*` imports and the cross-language simulation theorem remain future proof
targets.

## Semantic discrepancies

Proof failures and differential mismatches are expected engineering output.
The `bugs/` directory defines a versioned textual card with compiler phase,
pass occurrence, exact reproduction commands, expected and actual semantics,
proof evidence, classification, workaround, upstream tracking, and permanent
regression links. `make bug-cards` enforces that structure.

## External references

Upstream Lean supplies extensive structural and type-shape checkers for LCNF
and lower IR, but FIR does not assume a pre-existing complete operational
semantics or pass-correctness development. The closest background for the
lower reference-counting design is *Counting Immutable Beans*.

For WebAssembly, the official core specification remains the normative
semantic reference. Talos (`cajal-technologies/talos`) supplies the executable
Lean semantics used by FIR's optional bridge. Wean (`pmatos/wean`) and
`aionescu/lean-wasm` are useful design references but are not dependencies.
