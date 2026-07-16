# FIR

FIR is a research workspace for executable semantics and compiler-correctness
proofs for Lean's `Lean.Compiler.LCNF` pipeline. It contains a phase-indexed
program model, a small-step interpreter for final impure LCNF, the interfaces
needed to state same-phase and lowering theorems, and a parallel symbolic
LCNF-to-WebAssembly backend.

The repository is pinned to Lean 4.32.0. The proof campaign works backwards
from final impure LCNF while the Wasm backend develops against the same
interpreter and semantic ABI. See `docs/pass-correctness-plan.md` for the
implemented foundation and the remaining proof order.

## Requirements

- Lean toolchain: `leanprover/lean4:v4.32.0`
- Lake from the pinned Lean toolchain
- `rg` for the placeholder scan
- Python 3 for the validation orchestrator
- Optional: `lean-beam` for fast Lean diagnostics

## Common Commands

```sh
make check
```

`make check` runs the build, examples, native-vs-LCNF validation, and
placeholder and bug-card scans. Use `make examples`, `make validate`,
`make inspect`, or `make bug-cards` for an individual layer. `make beam` checks
the consolidated Lean entrypoints and fixtures through Lean Beam. `make inspect`
remains a pass-checkpoint diagnostic; it is not the semantic oracle.

The optional Talos bridge is deliberately outside the default dependency
graph. After cloning its pinned revision with `make talos-setup`, validate the
adapter and executable scalar example with `make talos-check`.

Parallel proof and Wasm work uses dedicated branches and worktrees with an
integration-only `main`. See `AGENTS.md` for the normative rules and
`docs/parallel-development.md` for the maintainer workflow.

## Layout

Public imports are deliberately small: consumers import `Fir`, or the
individual umbrellas `Fir.LeanIR` and `Fir.Wasm`. Test programs and the legacy
baseline are not re-exported.

- `Fir/LeanIR/Phase.lean`: phase-indexed base, mono, and impure programs plus
  checked-program wrappers.
- `Fir/LeanIR/Runtime.lean`: abstract runtime values, heap, ownership
  operations, external requests, traces, and observations.
- `Fir/LeanIR/Interpreter.lean`: canonical small-step semantics and executable
  runner for final impure LCNF.
- `Fir/LeanIR/Pipeline.lean`: exact Lean 4.32 pass-order guards and the reverse
  proof campaign.
- `Fir/LeanIR/Checkpoint.lean`: opt-in capture of actual declaration groups
  immediately before and after the upstream `simpCase` pass.
- `Fir/LeanIR/PassCorrectness.lean`: same-phase and cross-phase correctness
  contracts, including heap observations modulo address renaming and garbage.
- `Fir/LeanIR.lean`: the public semantics and proof-infrastructure umbrella.
- `Fir/Wasm.lean`: the public semantic-Wasm umbrella.
- `Fir/LeanIR/InterpreterExamples.lean`: executable coverage for calls,
  closures, joins, cases, constructors, mutation, ownership, reuse, and
  externals.
- `Fir/Validation/`: the versioned observation protocol, compiler-generated
  source corpus, final-impure capture, structured codecs, and LCNF candidate.
- `FirValidationNative.lean` and `FirValidationLCNF.lean`: native oracle and
  compiler-backed candidate entrypoints used by `make validate`.
- `Fir/Wasm/`: the semantic ABI and exhaustive symbolic lowering of impure
  LCNF.
- `integration/talos/`: optional pinned translation into Talos syntax and an
  executable Talos smoke test.
- `Fir/LeanIR/Legacy.lean` and `LegacyExamples.lean`: the original small
  evaluator, isolated as a differential fixture.
- `Inspect`: legacy coverage and real `simpCase` checkpoint diagnostics.
- `docs/validation.md`: corpus, artifacts, comparison contract, and the
  deferred V8/Talos backend handoff.
- `docs/research.md`: Lean IR and Wasm formalization research notes.
- `docs/lcnf-to-c.md`: pass-by-pass guide from Lean expressions through LCNF
  to direct C emission.
- `docs/pass-correctness-plan.md`: phase-aware semantics and compiler-pass
  correctness roadmap.
- `docs/parallel-development.md`: worktree ownership, synchronization, and
  integration workflow for concurrent agents.
- `bugs/`: textual semantic-discrepancy cards, their required format, and
  links to permanent regression tests.
