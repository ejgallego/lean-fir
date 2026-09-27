# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
functional-head: 870e70aa7281a8df1a9192e26eab0b6be6f2c6e6
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Compose fresh publication and destination binding into the ordinary code core with the original caller entry and suspended resource stack.
files: integration/talos/FirTalos/ConcretePublicationBind.lean; TrustAudit.lean; TrustInventory.lean; retained-initializer consumer/gate; W6 plans; this snapshot.
contracts: W6 proof helpers only. No shared semantic or ABI change. Two source steps match eight target suffix steps. The intermediate bind focus is constructed, the saved join environment restored and only the destination reuse fact erased. Central heap-miss admission remains unchanged.
checks: Beam helper/consumer checks, fresh batch downstream cone and exact-source retained reproduction/direct consumer pass. Candidate-wide gates and exact clean head are reported in the mailbox.
trust: 277 generic endpoints and fourteen checked-input consumer audits. Publication/bind composition retains the existing byte-assembly debt; the real-input endpoint additionally retains source-boxing debt. No new axiom.
bug-cards: None new. Existing retained-token ordinaryness and native-audit debt are unchanged.
blockers: Production Array external refinement, target callee execution and central heap-result lazy-miss closure remain separate obligations.
handoff: Seven-step publication 870e70aa7 remains immutable on W6-ROOT-20260927-003. This publication/bind successor is separate from that review and retains its accepted contract base 2504f9f74.
next: Connect production Array contracts and target callee prefix for RetainedRC2; retain/derive construction provenance and residual validation for central heap-miss admission. Publication/bind resource-stack assembly is now proved. No complete compressStored, resident-linking or encoded-byte theorem is claimed.
```
