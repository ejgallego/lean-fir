# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: e7610b9f9489286af7e2915cea78188372ed8c8f
functional-head: e7610b9f9
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Derive all five initializer binding-kind lookups from production local collection/refinement and remove them from the cold-cache endpoint.
files: ConcreteGeneratedLocals.lean; trust inventory/audit; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Same thirteen source transitions and matching target execution, with five fewer static premises. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Generic lowering recovery uses standard axioms; retained cold-cache endpoint keeps its exact dependency inventory.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Cold-cache entry checkpoint e7610b9f9 remains immutable under root review. Binding-kind premise removal is its separate successor; exact gates are in the mailbox.
next: Construct the initializer's generated declaration row internally from the supported pipeline, then connect the caller let to the staged invocation. Caller/resource and host contracts remain; no full compressStored or encoded-byte theorem is claimed.
```
