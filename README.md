# FIR

> [!CAUTION]
> **Internal, non-official research workspace — not for external use.**
>
> FIR is an unfinished implementation and proof experiment. It is not an
> official Lean project, specification, product, or supported toolchain
> component. It carries no promise of API or ABI stability, correctness,
> security review, release cadence, production readiness, or user support.
>
> Do not depend on its code or artifacts, cite it as a reference
> implementation, or treat this repository as public documentation. Unless
> you are an invited collaborator, please stop here.

FIR is a research workspace for executable semantics and compiler-correctness
proofs for Lean's `Lean.Compiler.LCNF` pipeline. It contains a phase-indexed
program model, a small-step interpreter for final impure LCNF, the interfaces
needed to state same-phase and lowering theorems, and two executable
LCNF-to-WebAssembly paths: FIR's symbolic backend and Lean's direct C emitter
followed by an optimized LLVM WebAssembly backend.

The repository is pinned to Lean 4.33.0. The proof campaign works backwards
from final impure LCNF while the Wasm backend develops against the same
interpreter and semantic ABI. See `docs/pass-correctness-plan.md` for the
implemented foundation and the remaining proof order.

## Requirements

- Lean toolchain: `leanprover/lean4:v4.33.0`
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

The repository has two native Wasm artifact generators. The FIR-native path
under `integration/talos/artifact` exposes the symbolic lowering and
incrementally linked resident runtime used for semantic and refinement work.
The compiler-native path under `integration/lcnf-c-wasm` sends the same final
impure LCNF through Lean's C emitter and Emscripten/LLVM, linking the pinned
Lean runtime, `Init`, and `Std`. They are complementary backends, not two
loaders for one artifact ABI. See `docs/wasm-artifact-generation.md` for the
selection guide and exact contract boundary.

Parallel proof and Wasm work uses dedicated branches and worktrees with an
integration-only `main`. See `AGENTS.md` for the normative rules and
`docs/parallel-development.md` for the maintainer workflow.

## Layout

The internal import surface is deliberately small: code in this workspace
imports `Fir`, or the individual umbrellas `Fir.LeanIR` and `Fir.Wasm`. Names
marked public refer only to Lean module visibility within this experiment, not
to a supported external API. Test programs and the legacy baseline are not
re-exported.

- `Fir/LeanIR/Phase.lean`: phase-indexed base, mono, and impure programs plus
  checked-program wrappers.
- `Fir/LeanIR/Runtime.lean`: abstract runtime values, heap, ownership
  operations, external requests, traces, and observations.
- `Fir/LeanIR/Interpreter.lean`: canonical small-step semantics and executable
  runner for final impure LCNF.
- `Fir/LeanIR/Pipeline.lean`: exact Lean 4.33 pass-order guards and the reverse
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
- `integration/talos/artifact/`: FIR-native symbolic Wasm artifact and
  resident-runtime generation, with Node/browser acceptance clients.
- `integration/lcnf-c-wasm/`: compiler-native LCNF-to-C-to-Wasm generation;
  Emscripten is primary, the freestanding profile is deliberately narrow, and
  the WASI profile is frozen.
- `Fir/LeanIR/Legacy.lean` and `LegacyExamples.lean`: the original small
  evaluator, isolated as a differential fixture.
- `Inspect`: legacy coverage and real `simpCase` checkpoint diagnostics.
- `docs/validation.md`: corpus, artifacts, comparison contract, the active
  shared-provider V8 path, and the planned Talos backend handoff.
- `docs/research.md`: Lean IR and Wasm formalization research notes.
- `docs/lcnf-to-c.md`: pass-by-pass guide from Lean expressions through LCNF
  to direct C emission.
- `docs/wasm-artifact-generation.md`: comparison and selection guide for the
  FIR-native and compiler-native Wasm artifact paths.
- `docs/pass-correctness-plan.md`: phase-aware semantics and compiler-pass
  correctness roadmap.
- `docs/parallel-development.md`: worktree ownership, synchronization, and
  integration workflow for concurrent agents.
- `bugs/`: textual semantic-discrepancy cards, their required format, and
  links to permanent regression tests.

## License

FIR is licensed under the Apache License 2.0, matching Lean and Verso. See
[LICENSE](./LICENSE) for the full terms. This license does not make FIR an
official or supported Lean project.
