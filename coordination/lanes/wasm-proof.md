# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 94fe90bb7d887efefee0df97f105931413764347
functional-head: 94fe90bb7
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Compose both captured literal lets with mkEmpty execution, starting at the actual initializer body and deriving the capacity value.
files: ConcreteLiteralPrefix.lean; trust inventory/audit; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Reusable immediate-scalar and bounded tagged-natural rules preserve runtime/store/witness exactly. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: Two generic literal endpoints use only standard axioms. Retained body-prefix composition adds one closed UInt8/tagged ABI native check to the previous mkEmpty endpoint's audited dependencies; no execution or heap claim uses native evaluation.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Actual captured mkEmpty checkpoint 94fe90bb7 is accepted main. Literal-prefix composition is the next isolated checkpoint; exact gates are in the mailbox.
next: Connect UInt8 boxing, fresh tagged push and return, then thread hereditary resource scope into the existing publication suffix. Current endpoint starts at the actual body and derives five source steps; no complete initializer, compressStored or encoded-byte theorem is claimed.
```
