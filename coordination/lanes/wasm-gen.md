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
base: 3536a3dff0b3ce3c9dfa65d516284fbe445bc523, accepted main containing the deleted-allocation semantic carrier and mailbox CLI cutover
functional-head: 734ed7c2d5aa744560ea813b2aae33e08bf666b8
contract-base: e2b0ae51775e9736c28d0ba5043203a73b06a31e; consumes the accepted precise direct-call and Float32 generation stack while changing no semantic ABI, helper signature, concrete layout, allocator, or ownership contract
clean-at-update: true
slice: Propagate reviewed conditional result kinds through compiler single-assignment locals and specialize only compiler-shaped checked releases from their exact symbolic operand kind. Definite `.tagged` releases disappear; definite `.object` releases select the existing unchecked operation; `.tobject`, unknown kinds, multiply assigned locals, and unrecognized instruction shapes remain checked. The first semantic transfer is upstream-shaped `Nat.sub`: a tagged left operand bounds the result to tagged because `left - right <= left`. Release normalization refreshes the complete operation/import frontier before persistent planning so newly selected unchecked decrements are internalized.
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; Fir/Wasm/Emit/ResidentCallSite.lean; Fir/Wasm/Emit/ResidentLinker.lean; Fir/Wasm/Emit/ResidentRelease.lean; bugs/FIR-BUG-wasm-none-late-release-specialization-frontier.md; integration/lean-zip/README.md; coordination/lanes/wasm-gen.md
contracts: no shared contract change. Conditional result refinements are provider-reviewed transfer facts over existing ABI kinds; release specialization retains every checked fallback and uses the stable resident decrement helpers. Helper names/signatures, semantic ABI, concrete layouts, allocator, ownership, public exports, and canonical package pointers are unchanged.
checks: Lean Beam refresh passed ResidentCallSite, ResidentBigNumeric, ResidentRelease, and ResidentLinker with zero diagnostics; CallSite and Release saved, while the two importer saves reported only dependency-barrier refresh advice and were replaced by a successful 55-job focused batch cone. git diff --check passed. make check passed with 719 source cases, 9 direct-machine cases, 728 unique cases, and 2166/2166 comparisons equal. make talos-setup completed and make talos-check passed all 3180 jobs. bash integration/talos/artifact/check.sh passed instruction provenance, every resident helper, deterministic plain/styled prettyM generation, Node/browser stack safety, the full 719-case V8 cone, and concrete readiness.
evidence: the lean-zip symbolic release census falls from 4478 to 4329 sites: 47 exact-representation sites plus 102 tagged-left Nat.sub result sites are erased, while 109 unproved Nat.sub-derived sites remain checked. On the accepted pre-integration runtime base, complete lean-zip is 366765 bytes with zero imports and SHA-256 68bbcebf59d0b9ce24a62eebf570147b4ff56a7a5bb29ec98f48c8b6f3af7295; the separately captured 16-pair screen had median ratio 0.9800523271 with 15/16 wins and remains screening, not an attributable performance claim. The final integration gate produced deterministic plain prettyM at 83982 bytes/SHA-256 b843f04ea92a6aab932c935e7943df4ca6efae59903330af8b022904dd5669fc and styled prettyM at 87396 bytes/SHA-256 b67f6154c475bb5fefaf96988e589be2cc3cab6692e88f78c8c1c49dfe05e2ce.
bug-cards: FIR-BUG-wasm-none-late-release-specialization-frontier fixed; the regression is the first unchecked decrement introduced only after precise Float32 result discovery
blockers: none for generation integration. W6 review of the conditional result transfer and release erasure remains a separately queued proof concern and does not change the stable executable boundary.
handoff: Functional head 734ed7c2d5aa744560ea813b2aae33e08bf666b8 is already fast-forwarded to main after rebasing on exact base 3536a3dff0b3ce3c9dfa65d516284fbe445bc523. Integrate this clean tracked status commit next; do not advance the canonical lean-zip package pointer from this slice.
next: Rebase the heap-only USize contract candidate onto this accepted main, stack the active LCNF and W6 adaptations in dependency order, implement the W7 resident USize box/unbox helper, and close the seven-family zero-frontier ratchet.
```
