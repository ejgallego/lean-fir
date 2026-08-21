# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3f4f7f2a, the refreshed W7 direct-result Nat.add handoff on accepted main 90ac4bad
functional-head: 8553f720
contract-base: 90ac4bad, including the accepted generic typed-object round-trip theorem; W7 generation head 3f4f7f2a is the exact proof parent. Transparent impure-hygiene work remains separately isolated at ad6e0ff3 under W6-W7-20260820-021
clean-at-update: true
slice: Adapted the exact generated Nat.add two-immediate arm from the scratch-slot cast to typedObjectWordRoundTripSource/unsignedI32RoundTrip. Source adaptation and target execution now preserve the exact naturalSum word, complete store and memory, and caller tail without scratch locals or a page-positivity premise. The operation theorem requires ValueRel at tobject for the semantic tagged Natural payload, admitting its canonical immediate or promoted live-heap representation while rejecting an arbitrary i32. The existing tagged-result termination theorem instantiates that relation; the opaque checked one-limb and multi-limb fallback is structurally unchanged.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: none changed. This is the W6 proof adaptation to W7 functional generation 04d54c38 and ratchet c7d38522. No emitter, ABI, layout, helper signature, ownership behavior, naturalSum implementation, local array, checked fallback, or shared semantic contract changed.
checks: W7's refreshed exact-parent handoff 3f4f7f2a records `git diff --check`, the complete artifact gate (44 concrete artifacts and 15 source probes), deterministic prettyM publication 4cdbc25835e5-e89b28ad7e6d6f52, and `make check` passing. On the combined W6 candidate, Lean Beam sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash 70d06a2f88bdd447); `lake -d integration/talos build FirTalos.ConcreteResidentNat` passed (3,078 jobs); `git diff --check` passed; `make check` passed (713 unique cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests); `make talos-setup` refreshed Talos 0e05edbc; and `make talos-check` passed (3,167 jobs). A redundant combined artifact rerun in the W6 worktree passed resident package/tool tests and resident global, memory, allocator, array, ByteArray, fixed-width, Float, and libm-frontier generation before stopping solely because this proof worktree has no local `.deps/lcnf-c-wasm/.../emcc`; the exact W7 parent carries the required complete artifact pass.
bug-cards: none
blockers: none
handoff: Integration should fast-forward main from 90ac4bad to the containing W6 status commit, thereby landing W7 functional generation 04d54c38, ratchet c7d38522, refreshed W7 handoff 3f4f7f2a, W6 proof 8553f720, and this status atomically. Do not expose the stale-proof W7 prefix separately.
next: After atomic acceptance, close W7-W6-20260820-015 and process the separately isolated impure-hygiene contract ad6e0ff3 with its two known W6 consumer adaptations.
```
