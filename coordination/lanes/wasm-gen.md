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
base: d113b550 on clean local main, including the accepted unified checked Natural-add fallback theorem and cached self-tail ownership fixture
functional-head: 5064d7cb, rebased opt-in early finite-target closure lowering; proof request W7-W6-20260823-008 retains its exact pre-constructor equivalent 108ddeda
contract-base: d113b550. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed. Closed packages derive module-local closureDispatch and closureDescriptors tables from retained operations; W6 proof adaptation is required before integration
clean-at-update: true
slice: Threaded the final-LCNF pap target set into compileClosureDispatch at the existing closed-package capability. Candidate declarations are filtered once per module; ordinary lower and lowerDecl retain the all-target path. The existing structural pass remains a fail-closed validator. The closed module's exact retained closure operations determine its module-local target and descriptor tables
files: Fir/Wasm/Lower.lean; Fir/Wasm/WellFormed.lean; Fir/Wasm/Emit/Source.lean; Fir/Wasm/Emit/SourceExamples.lean; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: Raw lean-zip retains 734 candidates and avoids constructing 10888 others. Closed metadata is 23 dispatch rows and 38 descriptor rows versus generic 439 and 194. Replacing only those two module-local arrays with the generic post-pass arrays makes the complete symbolic module exactly equal; normalized encoded bytes are exact. Generic opaque ingress is unchanged
performance: Preserving historical all-target metadata erased the optimization and was rejected. One noisy controlled raw run measured generic lowering at 30929ms and finite-target lowering at 18443ms; host load varied heavily, so this is directional evidence only. Before the independent constructor bridge, closure selection reduced the exact styled prettyM artifact from 85418 to 83521 bytes with the same 314 final functions. With the now-accepted constructor bridge composed, the fully gated candidate is 82370 bytes; this is exact module-size evidence, not a runtime-speed claim
checks: No system /tmp input was used; TMPDIR was the worktree-local .deps/tmp directory. Lean Beam PASS with zero diagnostics for Lower, WellFormed, Source, and SourceExamples. The combined 58-job SourceExamples/ResidentLinker cone PASS. git diff --check PASS. Exact make check PASS: 723 unique cases, 2151/2151 comparisons, 8565 machine steps, 194 active bug cards, all 25 mailbox tests. Complete W7 artifact gate PASS at rebased head 67628e35: deterministic double generation, checksum/package verification, atomic installation, zero-import resident fixtures, Node/raw/browser clients, styled trace, stack stress, native/LCNF/V8 differential cone, concrete readiness, scratch/ownership. Plain prettyM is 79002 bytes, SHA-256 5a1c84da88eb64ece73c1d4ff9be10f11350f9cadd17cbdd1c29afa73263fd69; styled trace is 82370 bytes, SHA-256 169e145f72cfe1b5009c26ce9f38065e48730ac4f5888f915e639e30fdd5f2ad, with 314 final functions and 23901 origins. The immutable evidence package is integration/talos/artifact/_build/prettyM-current-releases/67628e353b7b-6461e73f3856e0c7 and is not a publication pointer. make talos-check passes 3171 of 3172 targets and reports exactly one failure: W6-owned ConcreteClosureDispatch line 450 still states candidatesEq over context.program.decls; every other target passes
bug-cards: none; no semantic discrepancy was observed
blockers: W6 must first finish the public natAddFunction representation dispatcher over its accepted checked fallback, then adapt ConcreteClosureDispatch.instructions_compileClosureDispatch to the selected declaration array and state the closed-ingress premise. Until the closure proof compiles and Talos passes, this candidate must not land and dependent prettyM/lean-zip packages must not publish
handoff: The current rebased generation commit is 5064d7cb on exact main base d113b550. W6 may continue from request W7-W6-20260823-008 and its equivalent standalone 108ddeda proof input after completing the Natural-add dispatcher; integration will validate and land the generation/proof pair atomically
next: W6 public Natural-add dispatcher, then the selected-declaration closure proof; rerun all Talos jobs; then regenerate prettyM and lean-zip contracts and complete artifact gates as separate W7 consumer commits. Do not add another dependent generator slice to this branch until the closure pair serializes
```
