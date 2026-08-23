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
state: ready
base: 00f5a6a4 on clean local main; the standalone commit applies independently even though it was validated above the proof-pinned early-closure candidate
functional-head: 9e739895, scratch-free typed constructor result bridge
contract-base: 4505c592. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, allocation extent, or final constructor byte changed
clean-at-update: true
slice: Heap constructor helpers return the allocator's already-valid wasm32 address through the established typed i64-extend/i32-wrap bridge. This removes two scratch-memory loads, two stores, and two locals; Binaryen erases the physical round trip. Immediate constructors are unchanged. The manifest declares resultRetype typed-extend-wrap and scratchPolicy untouched, and the generated-shape guard pins the one-local/load-free helper suffix
files: Fir/Wasm/Emit/ResidentConstructor.lean; Fir/Wasm/Emit/ROADMAP.md; integration/talos/artifact/resident-constructor-client.mjs
contracts: none. The standalone fixture preserves zero imports, the exact 64-byte constructor layout, poisoned arena reuse, allocation frontier, memory growth, and every byte below heapBase. Future W6 resident-constructor implementation proofs should target the scratch-free suffix; no existing proved helper contract or signature changed
checks: Lean Beam update/sync/save PASS with zero diagnostics. Focused artifact Lake build PASS (95 jobs). Standalone Node constructor fixture PASS and shrinks from 981 to 935 bytes, SHA-256 7e2d06e1fadf426c338ee9a6255f3a3ce6b6ceabf8f4ceffbc3943f78737035b. git diff --check PASS. Exact make check PASS: 717 unique cases, 2133/2133 comparisons, 7947 machine steps, 193 bug cards, and all 25 mailbox tests. Complete W7 artifact gate PASS: deterministic generation, checksum/package verification, atomic installation, zero-import resident fixtures, Node/raw/browser clients, styled trace, stack stress, native/LCNF/V8 differential cone, concrete readiness, scratch/ownership. On the same early-closure candidate, plain prettyM is 79002 bytes, SHA-256 5a1c84da88eb64ece73c1d4ff9be10f11350f9cadd17cbdd1c29afa73263fd69; styled trace is 82370 bytes, SHA-256 169e145f72cfe1b5009c26ce9f38065e48730ac4f5888f915e639e30fdd5f2ad, with 314 final functions and 23901 origins. make talos-check still reports exactly the pre-existing ConcreteClosureDispatch line 450 failure among 3172 targets; the constructor slice adds no proof failure
bug-cards: none; no semantic discrepancy was observed
blockers: none for this standalone slice. The parent early-closure commit 108ddeda remains separately blocked on W6 request W7-W6-20260823-008 and must not land with this commit
handoff: Integration should cherry-pick only 9e739895 onto current main, validate the focused constructor module/client, and record the exact result. Do not fast-forward the containing wasm/generation branch because it also contains the proof-blocked early-closure candidate
next: After this independent landing, rebase wasm/generation on main and restore the tracked early-closure waiting handoff. Once W6 adapts the selected-declaration theorem, land that generation/proof pair atomically and regenerate prettyM and lean-zip consumer packages
```
