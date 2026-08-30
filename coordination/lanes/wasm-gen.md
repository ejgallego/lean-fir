# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: 0b942424927517a7ac20c627270ea0653a5eac52, exact accepted main after required shared-contract rebase
functional-head: e19d86d51ac7fe5cb6a870b7c6ab3e936a65fe71
contract-base: 0b942424927517a7ac20c627270ea0653a5eac52; isolated shared ABI/lowering contract commit c56680f3f7926ae979768a41d7d840a911d72989 awaits integration review
clean-at-update: true
slice: Preserves the complete promoted object tag during source object-case lowering and resident execution. getTag now has tobject -> UInt64 ABI, object cases compare with i64.eq, constructor allocation retains its separate UInt32 bound, the resident helper returns exact promoted payloads, and a generated zero-import object-case fixture proves that promoted tag 2^32 selects the default rather than aliasing constructor zero.
files: Fir/Wasm/ABI.lean; Fir/Wasm/Lower.lean; Fir/Wasm/Examples.lean; scripts/wasm_semantic_host.mjs; Fir/Wasm/Emit/ResidentRuntime.lean; Fir/Wasm/Emit/Examples.lean; integration/talos/artifact/{FirWasmArtifactMain.lean,concrete-corpus.mjs,concrete-host.mjs,resident-get-tag-client.mjs,resident-tag-setter-client.mjs,run-resident-object-case.mjs,test-concrete-readiness.mjs,test-semantic-host.mjs,check.sh,README.md}; this lane status
contracts: Shared Wasm ABI/lowering contract changes getTag result from UInt32/i32 to UInt64/i64 and uses the widened value only for object-case comparison. Allocation/header tags remain UInt32-bounded. Resident helper signature changes correspondingly; ownership and concrete object layout are unchanged.
checks: Lean Beam refresh/sync/save passed for ABI, Lower, source examples, ResidentRuntime, and emitter examples. git diff --check passed. node --check passed for the changed clients and host. integration/talos/artifact/test-semantic-host.mjs passed. Focused lake build Fir.Wasm.Examples passed 13 jobs; nested lake build fir-wasm-artifact passed 95 jobs. Generated promoted-tag-case (107 bytes, SHA-256 2d806eb2...), resident-get-tag (237 bytes, 6e614269...), and zero-import resident-object-case (361 bytes, 2a56807a...); all focused Node executions passed. make check passed 730 unique cases and 2172/2172 comparisons with 213 active bug cards and 38 mailbox tests. make talos-setup passed. make talos-check reached 3086 green jobs and then failed only at the expected stale W6-owned FirTalos/Runtime.lean:880 getTagStep UInt32 result; final Talos/artifact gates await that proof/runtime adaptation.
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation, owned by W6
blockers: Ordinary W6 dependency: adapt getTagStep and its refinement cone to the isolated UInt64 contract, then return an exact clean checkpoint. Authoritative thread W6-W7-20260830-003 tail W7-W6-20260830-002.
handoff: Not yet ready for integration. Root may review rebased isolated contract commit c56680f3 through W7-ROOT-20260830-001, but must serialize it with the W6 adaptation before landing the complete slice.
next: Consume the W6 checkpoint, rerun make talos-check and integration/talos/artifact/check.sh, ratchet any deterministic W7 artifact deltas, publish a clean ready checkpoint, and hand the dependency-ordered stack to root.
```
