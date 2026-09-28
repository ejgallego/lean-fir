# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: bf1f22fe07f45ebf830acbc51e7ed3f950362693
functional-head: bf1f22fe0
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Preserve the original construction entry through external staging, host execution and binding; consume the rules in retained Array.push.
files: ConcreteRegionExternal.lean; ConcreteArrayPushCall.lean; RetainedArrayCalls.lean; TrustInventory.lean; W6 plans/README and this snapshot.
contracts: Staged call and pre-bind relations retain fixed-entry resource scope and region closure. Push derives region preservation from its actual response; caller no longer reconstructs the post-push relation. Public thirteen-/fourteen-step APIs, central admission, shared ABI/semantics and emitter unchanged.
checks: Beam, clean local FirTalos rebuild of focused cone/audit, forced direct changed generic modules/audit, make check and Talos setup/check pass. Exact-source retained reconstruction/readback and forced direct consumers pass, including cutoff regression and 25 retained audits. Generic inventory now has 317 endpoints. Exact clean head in mailbox; RC2 native-compiler caveat unchanged.
trust: No new native evaluation or axiom. Three new generic rules use only standard Lean axioms; retained endpoint inventory unchanged.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Active construction checkpoint bf1f22fe0 is accepted main. External-state closure is a separate successor; exact gates go in mailbox.
next: Apply region call/bind rules to empty Array allocation and expose literal/boxing states, then package the saved validated caller for general lazy frames. Do not drop object/tobject exclusions by fiat. Installed handlers and whole compressStored/encoded-byte correctness remain separate.
```
