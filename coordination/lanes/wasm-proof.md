# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: ace34e08aca1cf8755508c6736130051a6724236
functional-head: ace34e08a
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Preserve the original export result kind through the completed initializer block and reconnect its caller to the rooted global simulation.
files: RetainedArrayCalls.lean with exact endpoint audit; W6 plans/consumer README and this snapshot.
contracts: Rooted fourteen-source-step block with matching target execution and precise global endpoint at the evolved witness. No root-equals-object, future return or new invariant premise. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Retained rooted execution keeps the existing exact dependency inventory.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Caller-let checkpoint 54bc0b007 is accepted main; validated composition ace34e08a is separately submitted. Root transport is an independent successor; exact gates are in the mailbox.
next: Prove closure at intermediate heap-result lazy frames without dropping object/tobject exclusions by fiat. Installed-handler conformance and whole compressStored/encoded-byte correctness remain separate.
```
