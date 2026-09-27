# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 54bc0b007b442c1ebd6fa7b513229b829b072ab4
functional-head: 54bc0b007
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Derive lazy-call admission from caller validation and preserve the validated caller relation through the complete initializer execution.
files: ConcreteValidatedLet.lean; trust inventory/audit; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Validated-to-validated fourteen-source-step block with matching target execution; no separate call admission, cache alignment, local-kind or continuation-validation premise. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Both generic validation helpers use standard axioms; retained execution keeps the existing exact dependency inventory.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Caller-let checkpoint 54bc0b007 is accepted main. Validated-to-validated composition is the next separate checkpoint; exact gates are in the mailbox.
next: Connect bounded heap-result execution to the central simulation/precise-result boundary without dropping object/tobject exclusions by fiat. Installed-handler conformance and whole compressStored/encoded-byte correctness remain separate.
```
