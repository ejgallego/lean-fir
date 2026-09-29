# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/fresh-lazy-steps-4341
worktree: .worktrees/wasm-talos
state: active
base: 60c3c1b07e4d912ffe622718f5a6c59267c2e3d6
functional-head: 60c3c1b07e4d912ffe622718f5a6c59267c2e3d6
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Saved lazy caller through external staging, host response and destination bind; retained stepwise consumer.
files: ConcreteFreshLazyExternal.lean; ConcreteArrayExternalCall.lean; RetainedArrayCalls.lean; trust inventory/umbrella; W6 plan/README; this snapshot.
contracts: The temporary external destination bind is distinguished from the saved lazy stack. The retained framed body produces its publication input directly, without post-body caller reconstruction or a new public premise. Shared semantics/ABI, central admission and emitter unchanged.
checks: Beam, make check, make talos-setup/talos-check, focused batch and forced direct generic modules pass on 4.34.1. The exact retained recipe rebuilds the checked source, reads back 21 declarations and directly checks both consumers and their exact axiom inventories. Known retained native-codegen diagnostics persist. The exact clean candidate belongs to the canonical handoff, not this active snapshot.
trust: No new native evaluation or axiom. Generic frame transitions use standard Lean axioms; allocation and retained consumers inherit the already audited dependencies. A negative stack theorem rejects premature publication of an external result.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen remains a native-code-generation diagnostic caveat despite passing kernel/direct checks. New FIR-BUG-wasm-none-resident-host-observation-boundary has two checked negative regressions.
blockers: Central heap-miss closure still needs general intermediate/nested frame composition and existing-persistent-result provenance. Resident linking needs a memory/observation bridge: a host-preserving helper cannot match an added source external event under the unchanged host-trace relation.
handoff: Predecessor 60c3c1b07 is preserved unchanged on wasm/talos-runtime for root review. This separate successor is proof-only; root consumes only its separately published exact clean gated checkpoint.
next: Lift the individual push transitions, then compose the general nested construction dispatcher; preserve fresh versus existing-persistent result distinction. Resident observation/erasure and handler conformance remain separate obligations.
```
