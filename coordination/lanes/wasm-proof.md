# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: b25df81ce519f090229e488e8bf0a2e1a111f52c
functional-head: b25df81ce
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Construct the fresh-result return relation from actual initializer execution and consume it at rooted publication.
files: ConcreteFreshYield.lean; ConcretePublicationValidation.lean; RetainedArrayCalls.lean; trust inventory; W6 plans/README and this snapshot.
contracts: Dynamic return relation stores original entry scope, represented heap result and producer region evidence. Actual retained body constructs it; generic publication rejoins the existing rooted global relation. Central admission policy, shared semantics/ABI and emitter unchanged.
checks: Beam, focused batch cone, forced direct new modules/310-endpoint audit, make check and Talos setup/check pass. Retained reconstruction/readback and 25 exact audits exit 0; accepted predecessor and candidate both emit the existing RC2 projection panic diagnostic. Exact checkpoint in mailbox.
trust: No new native evaluation or axiom. Return constructor uses propext/Quot.sound; publication inherits existing byte-assembly debt. Retained endpoint inventory unchanged.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: One-step publication checkpoint b25df81ce is accepted main. Fresh-result state is a separate successor; exact gates go in the mailbox.
next: Retain saved caller and construction-region evidence through general intermediate initializer states and lazy entry, connecting the fresh return state without dropping object/tobject exclusions by fiat. Installed handlers and whole compressStored/encoded-byte correctness remain separate.
```
