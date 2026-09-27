# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 598cfda1bf69520f755bcc60f6b55be8bcbdb69b
functional-head: a696ae515
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Factor representation-independent external staging and call execution out of the existing pure-family admission.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; TrustInventory.lean; W6 plans/consumer README; this snapshot.
contracts: W6 proof-side shape/focus factoring only. Generic rules accept ExternalCallShape and ConcreteExternalCallEvidence; old pure structures extend them and delegate to the common proofs. No shared semantic/ABI or central admission-policy change.
checks: Beam full-file check, fresh batch central-module build, make check, Talos setup/check and retained reconstruction/readback/direct consumer pass. Rebased candidate gates are reported at the exact clean mailbox checkpoint.
trust: 287 generic endpoints; two generic rules and two compatibility endpoints have only standard Lean axioms. Array evidence retains existing byte-assembly debt. No new axiom.
bug-cards: None new. Existing retained-token ordinaryness and native-audit debt are unchanged.
blockers: Production Array external refinement, target callee execution and central heap-result lazy-miss closure remain separate obligations.
handoff: Tagged-push aa33f5e13 landed patch-identically as a696ae515 on main 598cfda1b (ROOT-W6-20260927-008). Generic external-control factoring is a separate successor; exact clean candidate is published in the mailbox.
next: Instantiate generic external shape/staging/call rules from checked RetainedRC2 declaration/lowering facts, connect both Array evidence constructors and destination binding. Retain construction provenance/residual validation for heap-miss admission. Handler installation/resident linking remain separate; no complete compressStored or encoded-byte theorem.
```
