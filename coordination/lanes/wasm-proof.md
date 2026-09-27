# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 3a6958e28050f9c27d489be89031a96f6a5070df
functional-head: 3a6958e28
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Connect the staged lazy miss to actual body execution and caller resumption, deriving initial callee frame and installed continuation stacks.
files: ConcreteLazyBodyEntry.lean; trust inventory/audit; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Derive thirteen source transitions and matching target execution to caller CodeCoreRel, retaining original outer scope and suspended stack. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Generic entry uses standard axioms; retained cold-cache endpoint has the same exact dependencies as body_returns.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Body-to-caller checkpoint 3a6958e28 is accepted main. Cold-cache entry composition is the next isolated checkpoint; exact gates are in the mailbox.
next: Derive the five binding-kind rows from production lowering of the checked declaration. Current theorem starts at a staged invocation and retains caller/resource and host contracts; no full compressStored or encoded-byte theorem is claimed.
```
