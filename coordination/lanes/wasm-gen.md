# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; client-specific contracts remain
inside their integration directories. This mailbox records only the active
queue and current handoff boundary.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 8c5fc9f1 on main
functional-head: d841cf83, align proof-indexed resident Array calls with Lean's trusted internal path
contract-base: 8c5fc9f1 on main. Consumes the accepted resident Array layout, ownership, copy-on-write, and caller-resumption contracts. Changes no semantic operation, concrete layout, symbolic-Wasm instruction, ownership rule, or resident-helper signature. Separates checked foreign-representation validation from erased-proof validation inside W7 generation and requests W6 refinement premises in W7-W6-20260814-002
clean-at-update: true
slice: Pin the Lean 4.33 resident Array conformance matrix and make proof-indexed getInternal/uget/get/set/uset/swap implementations trust their erased bounds premises, matching upstream's unchecked hot path. Trusted Nat indices use the direct lean_unbox shift shape; trusted USize indices narrow directly. Public helpers remain representation- and proof-checked, and dynamic get!/set! retain bounds/default behavior. Preserve allocation, recursive release, copy-on-write, and owned/borrowed results. Add compile-time instruction-shape ratchets plus a zero-import trusted closed module. Record the distinct missing recoverable-panic observation for dynamic out-of-bounds calls. Correct an accepted-main placeholder-scanner false positive in an error message. Record, without weakening, the stale lean-zip exact closure ratchet exposed by accepted G2 compiler-cache isolation
files: Fir/Wasm/Emit/ResidentArray.lean; Fir/Wasm/Emit/ARRAY_CONFORMANCE.md; Fir/Wasm/Emit/ROADMAP.md; Fir/Wasm/Emit/SourceExamples.lean; bugs/FIR-BUG-wasm-none-array-panic-observation.md; bugs/FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet.md
contracts: none
checks: Lean Beam update/sync/save passed ResidentArray with zero diagnostics. lake build Fir.Wasm.Emit.ResidentArray passed 19 jobs. The checked resident-arrays artifact and Node client passed. The real lean-zip raw closure compiled with 662 declarations, 128 reviewed externals, 2,598 resident helpers, zero unsupported declarations, zero runtime operations, and only its three intended math imports before zero-import linking; all five cases at ten compression levels matched native Lean and cache/checkpoint ownership passed. Same-main baseline/candidate A/B execution produced identical output digests and flat frontiers; frontier Wasm shrank 201 bytes, while the completely linked artifact grew 2,798 bytes and timing samples were noisy/inconclusive, so no performance claim is made. make bug-cards passed 178 active cards. make check passed 125 harness tests, 701 native/LCNF cases, 9 direct-machine cases, 701 native/LCNF/V8 cases, 710 unique cases, and 2,112/2,112 comparisons; trusted-assumption, no-placeholder, and mailbox checks passed. make talos-setup passed at Talos 0e05edbc; make talos-check passed 3,148 jobs. bash integration/talos/artifact/check.sh passed all resident standalone checks, source-emitter and deterministic prettyM package checks, Node clients, 701-case V8 differential validation with 2,103/2,103 backend results, 640 executable concrete shared-validation cases with the existing 61 ByteArray exclusions, and deterministic concrete artifact checks. git diff --check passed and the worktree was clean before this status update
bug-cards: FIR-BUG-wasm-none-array-panic-observation; FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet
blockers: none
handoff: Integration may land prerequisite commits 3e7b3c1a and 6305a8a3 followed by functional commit d841cf83 after resolving the actual wasm/generation branch head. Generation readiness is independent of the W6 refinement follow-up in W7-W6-20260814-002. The global semantic rule remains queued in W7-ROOT-20260814-003. Do not publish a new lean-zip package until its reviewed exact declaration inventory replaces the stale 702-declaration ratchet; the executable zero-import candidate itself is green
next: Have integration accept the Array slice, then rebase W7. W6 should classify/discharge the proof-indexed bounds premises without changing generation readiness. Separately review and update the lean-zip post-G2 closure inventory and publish the zero-import package. Design the resident panic-observation mechanism before claiming full dynamic Array behavioral equivalence; do not replace upstream's recoverable observation with a Wasm trap
```
