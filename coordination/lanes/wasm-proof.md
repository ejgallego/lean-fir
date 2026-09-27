# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: c2e698c929c4e674b3b253261db1e38985dcd6d4
functional-head: c2e698c92
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Construct the initializer's generated row internally and connect the actual caller let through lazy staging to full execution/publication/bind.
files: ConcreteLazyBodyEntry.lean; trust inventory; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Fourteen source transitions and matching target execution from caller let; no supplied callee row, staging step or ready state. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Generic staging uses standard axioms; both retained execution endpoints keep the existing exact dependency inventory.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Entry and binding-kind checkpoints e7610b9f9 and c2e698c92 are accepted main. Caller-let execution is the next separate checkpoint; exact gates are in the mailbox.
next: Derive call-site support from production validation at the caller let. Caller/resource and host contracts remain; installed-handler conformance, general heap-miss closure and whole compressStored/encoded-byte correctness are separate.
```
