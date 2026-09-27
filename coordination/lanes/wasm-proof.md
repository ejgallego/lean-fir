# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 9a6fdf291f49f60cfd5cb2ddad6d6d28757acbb3
functional-head: 9a6fdf291
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Carry existing operation transports through the retained body, derive its post-body resource scope, and compose publication/bind back to the caller.
files: ConcreteBodyResources.lean; ConcreteArrayPushCall.lean; ConcreteArrayExternalCall.lean; trust inventory/audit; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Derive twelve source transitions and matching target execution to caller CodeCoreRel, retaining original outer scope and suspended stack. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Three generic resource-transport endpoints use only propext/Quot.sound; composed publication endpoint has the same exact dependencies as body_returns.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Complete-body checkpoint 9a6fdf291 is accepted main. Body-to-caller publication is the next isolated checkpoint; exact gates are in the mailbox.
next: Derive body focus, initial callee resource frame and cache/call-frame layout from the actual lazy miss entry. Current theorem starts at that installed body entry; no full entry-to-caller initializer, compressStored or encoded-byte theorem is claimed.
```
