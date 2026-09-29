# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 3653117e008a7208ed5ae798bedf09b16886fe82
functional-head: 81bb0e2abfac0270f76844bb5d193dec945844e4
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Stepwise empty allocation/literals/boxing, saved validated lazy caller, and resident observation boundary.
files: ConcreteRegionCode.lean; ConcreteArrayExternalCall.lean; ConcreteLiteralPrefix.lean; ConcreteBoxPrefix.lean; ConcreteFreshLazyFrame.lean; ConcreteResidentBoundaryTests.lean; RetainedArrayCalls.lean; trust inventory/umbrella; W6 plans/README; bug card; this snapshot.
contracts: Original construction entry survives every retained initializer operation without whole-body reconstruction. Saved frame supplies exact caller/root/publication metadata; new retained thirteen-step consumer rejoins rooted global bind. Shared semantics/ABI, central admission and emitter unchanged.
checks: Beam and focused batch proof checks; exact-source retained rebuild, fresh 21-declaration readback and forced direct consumers pass on 4.34.1. Generic inventory has 324 endpoints; retained inventory has 26. Final ordinary checkpoint gates and exact clean candidate belong to the canonical handoff, not this active snapshot.
trust: No new native evaluation or axiom. Frame staging/entry/return use standard axioms; publication inherits the existing byte-assembly native dependency. Both negative resident-boundary theorems use only propext and Quot.sound.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen remains a native-code-generation diagnostic caveat despite passing kernel/direct checks. New FIR-BUG-wasm-none-resident-host-observation-boundary has two checked negative regressions.
blockers: Central heap-miss closure still needs general intermediate/nested frame composition and existing-persistent-result provenance. Resident linking needs a memory/observation bridge: a host-preserving helper cannot match an added source external event under the unchanged host-trace relation.
handoff: Previous external-state checkpoint 81bb0e2ab is accepted main. This successor is proof-only; root consumes only its separately published exact clean gated checkpoint.
next: Compose saved frames through the remaining intermediate dispatcher; preserve fresh versus existing-persistent result distinction. Resolve the resident observation bridge through root before claiming handler substitution/linking; helper bodies and encoded-byte correctness remain separate obligations.
```
