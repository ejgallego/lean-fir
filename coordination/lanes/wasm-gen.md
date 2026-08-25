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
state: active
base: 051a70e0 on clean local main, including the accepted generation/proof stack and exact consumer publication checkpoint
functional-head: 056b25a4, exposing the actual production releaseHeaderFunction to W6; consumer ratchet head 9813e9c8 and decrement proof-surface head 0f351de8 remain accepted
contract-base: 051a70e0. No Lean semantics, concrete layout, resident-helper body or signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed
clean-at-update: true
slice: Exposed the exact production releaseHeaderFunction installed by internalizeReleases so W6 can unfold its real callee without a copied proof body or caller-supplied certificate. The helper body, installation path, generated Wasm, and published consumers are unchanged
files: Fir/Wasm/Emit/ResidentCallSite.lean; Fir/Wasm/Emit/ResidentBigNumeric.lean; Fir/Wasm/Emit/ResidentNatArithmetic.lean; Fir/Wasm/Emit/ResidentRelease.lean; integration/talos/artifact package publication; integration/lean-zip package contracts and publication; Fir/Validation/Corpus.lean; validation plans; coordination lane and board records
contracts: The production decrement and header-release definitions are now definitionally visible to W6 and otherwise unchanged. Typed caller rewrites still fail closed on missing, duplicate, or signature-incompatible registrations, and final symbolic validation checks replacement bodies at actual caller stack boundaries
performance: The accepted typed-Nat batch improves the balanced level-6 median from 64.12ms to 52.55ms, about 18%, with 8/8 pairs improving; module size grows from 454918 to 478669 bytes. Nat.decLe was neutral at 45.24ms versus 45.36ms and was rejected. Checked increment factoring shrank the candidate module from 478669 to 414781 bytes but was neutral at 40.77ms versus 40.70ms with a +0.05ms paired median and 16/32 wins, so its emitter change was discarded under the runtime policy
checks: No system /tmp input was used; TMPDIR was worktree-local. The release-header surface passed Lean Beam update/sync/save with zero diagnostics and source hash e63d9ba40351c6f8, the 54-job emitter/linker cone, make check at 725 unique cases and 2157/2157 comparisons with 8959 machine steps, and all 3172 Talos jobs. The accepted deterministic prettyM and stored/Level-1/raw lean-zip publication gates remain green
bug-cards: FIR-BUG-wasm-none-selected-lowering-proof-surface is fixed; active W6 release proof records FIR-BUG-wasm-none-liveheaprel-canonical-header-words; no new W7 discrepancy
blockers: none
handoff: Proof-surface head 056b25a4 is ready above accepted main 051a70e0 for W6's active release refinement. Published package identities remain the exact ones recorded at 9813e9c8 and all remain module-memory and zero-import
next: W6 consumes releaseHeaderFunction, completes recursive release, and returns a clean production-bound proof handoff. FIX-W7-20260825-003 is the next independent fidelity integration; no new release-body optimization should begin before proof convergence
```
