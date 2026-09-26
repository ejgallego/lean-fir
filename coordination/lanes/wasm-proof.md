# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: f274f35c1374dc6f845032c9a716dbaea5e8ee77
functional-head: dc3926c0c6d2365bea89a25285f5208f27c9e469
contract-base: f274f35c1374dc6f845032c9a716dbaea5e8ee77
clean-at-update: false
slice: Install entry-indexed retained-caller transport in the central structured simulation.
files: integration/talos/FirTalos/ConcreteRetainedTransports.lean; ConcreteStructuredSimulation.lean; ConcreteStructuredValidation.lean; TrustInventory.lean; W6 plans; this snapshot.
contracts: W6 proof relation only. Active and suspended scopes use RetainedCodeEntryTransports. Exact inner-call completion composes back to the saved outer entry. Local legacy operation proofs are lifted without resetting that entry. Legacy whole-declaration ordinary-persistence conclusions and all physical/ABI contracts remain intact.
checks: Lean Beam update/sync and refreshed focused batch cone pass; make check, make talos-setup, make talos-check and the checked-input reproduction/direct consumer gate pass. Rebase and exact clean checkpoint are published in the mailbox rather than asserted by this editing-state snapshot.
trust: The expanded 271-endpoint inventory passes; five additions use only propext/Quot.sound. Existing source initializer boxing-policy native debt remains distinct; no new axiom dependency.
bug-cards: None new. Existing retained-token ordinaryness and native-audit debt are unchanged.
blockers: None for migration. Production Array external refinement, target callee execution and heap-result lazy-miss closure remain separate obligations.
handoff: Predecessor dc3926c0c was accepted as 7a6f004d4 on main d0fee1880 (ROOT-W6-20260926-015). The successor is not part of that immutable review; publish a new exact gated checkpoint after rebase.
next: Derive cumulative heap-publication transport at the lazy-miss consumer before lifting object/tobject exclusions; connect production Array contracts and the generated target prefix for the checked RetainedRC2 initializer. No complete compressStored, resident-linking or encoded-byte theorem is claimed.
```
