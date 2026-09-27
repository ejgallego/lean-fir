# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 503e9088357c96cd267fe280f77b66264b8f8dcb
functional-head: 503e90883
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Expose the one-step heap-cache publication boundary and reconstruct the validated rooted bind successor from the saved caller.
files: ConcretePublicationBind.lean; ConcretePublicationValidation.lean; trust inventory/audit; W6 plans/README and this snapshot.
contracts: One source publication step and seven target steps yield the existing rooted global externalBind outcome; old two-step consumer factors through this core step. No new invariant or central admission-policy change; shared semantics/ABI and emitter unchanged.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Both new endpoints retain the existing cache-publication byte-assembly dependency; retained execution keeps its exact inventory.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Construction-region checkpoint 503e90883 is accepted main. One-step publication re-entry is the separate successor; exact gates are in the mailbox.
next: Construct the pre-publication heap-return state retaining callee scope and producer region evidence, then wire central admission without dropping object/tobject exclusions by fiat. Installed handlers and whole compressStored/encoded-byte correctness remain separate.
```
