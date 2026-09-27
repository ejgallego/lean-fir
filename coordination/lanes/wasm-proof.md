# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 417c531eacc1ab51cd1953c5a9c70750c77fa6f8
functional-head: 417c531ea
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Carry producer region closure through empty allocation and in-place push, then preserve it through cache publication.
files: ConcreteRegionTransport.lean; ConcreteRetainedPublication.lean and scope consumer; trust inventory/audit; retained consumers; W6 plans/README and this snapshot.
contracts: Body returns construction-region evidence; publication returns surviving region and caller transport. No added client premise or central admission-policy change; shared semantics/ABI and emitter unchanged.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Generic region lemmas use standard Lean axioms; retained execution keeps its existing exact dependency inventory.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Rooted checkpoint 417c531ea is accepted main. Construction-region transport is the separate successor; exact gates are in the mailbox.
next: Retain the now-produced region evidence in intermediate heap-result lazy frames without dropping object/tobject exclusions by fiat. Installed-handler conformance and whole compressStored/encoded-byte correctness remain separate.
```
