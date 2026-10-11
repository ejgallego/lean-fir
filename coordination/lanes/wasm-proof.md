# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/fresh-lazy-push-main-4341
worktree: .worktrees/wasm-talos
state: active
base: 15dc1f46025a498474e39f5660bc82053d588dcf
functional-head: d3b3321dc
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Retain saved lazy caller through each actual Array.push transition.
files: ConcreteArrayPushCall.lean; RetainedArrayCalls.lean; TrustInventory.lean; W6 plan/README; this snapshot.
contracts: The temporary external destination bind is distinguished from the saved lazy stack. The retained framed body produces its publication input directly, without post-body caller reconstruction or a new public premise. Shared semantics/ABI, central admission and emitter unchanged.
checks: Beam, make check, accepted-overlay Talos setup/full proof and forced exact trust audit, focused/direct checks and the full retained initializer recipe pass on Lean 4.34.1. Native Talos candidate checks remain consolidation-owned; these results use the accepted overlay. Exact clean results belong to the canonical handoff.
trust: No new native evaluation or axiom. Generic frame transitions use standard Lean axioms; allocation and retained consumers inherit the already audited dependencies. A negative stack theorem rejects premature publication of an external result.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen remains a native-code-generation diagnostic caveat despite passing kernel/direct checks. New FIR-BUG-wasm-none-resident-host-observation-boundary has two checked negative regressions.
blockers: Central heap-miss closure still needs general intermediate/nested frame composition and existing-persistent-result provenance. Resident linking needs a memory/observation bridge: a host-preserving helper cannot match an added source external event under the unchanged host-trace relation.
handoff: Predecessor landed as f6850d79f; reviewed 8535c2a74 stays unchanged. Its patch is reproduced as d3b3321dc on accepted main for this continuation. Blueprint coordination is W6-BP-20261011-001. Native Talos candidate 38975b8a6 remains consolidation-owned until root integration.
next: Compose the general nested construction dispatcher; preserve fresh versus existing-persistent result distinction. Resident observation/erasure and handler conformance remain separate obligations.
```
