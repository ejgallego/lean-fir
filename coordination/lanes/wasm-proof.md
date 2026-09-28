# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 14be5c08bca91177fe033d13001a6bafeca22c19
functional-head: 14be5c08b
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Carry the active construction scope from cache-miss entry through retained construction blocks and the return step.
files: ConcreteRegionCode.lean; ConcreteRegionEntry.lean; RetainedArrayCalls.lean; trust inventory/audit; W6 plans/README and this snapshot.
contracts: Fixed-entry active relation initializes at actual lazy miss, transports through allocation/boxing/push blocks and yields the fresh-result relation at return. Exact caller frame equations survive; public thirteen-/fourteen-step APIs unchanged. Central admission policy, shared semantics/ABI and emitter unchanged.
checks: Beam, cutoff-negative regression, focused batch cone, forced direct new modules/314-endpoint audit, make check and Talos setup/check pass. Retained reconstruction/readback and 25 exact direct audits pass; documented RC2 compiler diagnostic caveat remains. Exact clean checkpoint in mailbox.
trust: No new native evaluation or axiom. Four new generic endpoints use only standard Lean axioms; retained endpoint inventory unchanged.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Fresh-result checkpoint 14be5c08b is accepted main. Active construction relation is the separate successor; exact gates go in mailbox.
next: Retain construction evidence across external-ready/bind states inside the blocks, and package the saved validated caller for general lazy frames. Do not drop object/tobject exclusions by fiat. Installed handlers and whole compressStored/encoded-byte correctness remain separate.
```
