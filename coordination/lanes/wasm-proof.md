# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: ef1c758a4cdfbcc7ebd25a218069ea3d4386d319
functional-head: 6b447fd0a7a0785e141bf08e4dd0ee7e35b275fe
contract-base: ef1c758a4cdfbcc7ebd25a218069ea3d4386d319
clean-at-update: false
slice: Restore the full caller scope after fresh heap cache publication; share restoration with the validated non-heap dispatcher.
files: integration/talos/FirTalos/ConcretePublicationScope.lean; ConcreteStructuredValidation.lean; TrustInventory.lean; retained-initializer consumer/gate; W6 plans; this snapshot.
contracts: W6 proof helpers only. No shared semantic or ABI change. Restoration composes to the original caller entry, including cache-table, external, capacity and closure-ABI facts. Non-heap admission and its target path remain unchanged.
checks: Beam helper/consumer checks, fresh batch downstream cone, make check, make talos-setup, make talos-check, exact-source retained reproduction/direct consumer and forced direct trust audit pass. Exact clean head is published in the mailbox rather than asserted by this editing-state snapshot.
trust: 275 generic endpoints and twelve checked-input consumer audits pass. Common restoration uses only propext/Quot.sound; fresh publication and the consumer retain the existing byte-assembly/source-boxing native debt. No new axiom introduced.
bug-cards: None new. Existing retained-token ordinaryness and native-audit debt are unchanged.
blockers: Production Array external refinement, target callee execution and central heap-result lazy-miss closure remain separate obligations.
handoff: Central retained stack landed at 1291fecaf. Fresh publication predecessor 6b447fd0a is separately immutable on W6-ROOT-20260926-016; this restoration successor is not part of that review.
next: Retain and derive construction provenance in the lazy-miss dispatcher, then assemble the complete heap-result publication/bind stack transition. Connect production Array contracts and target prefix for RetainedRC2. No complete compressStored, resident-linking or encoded-byte theorem is claimed.
```
