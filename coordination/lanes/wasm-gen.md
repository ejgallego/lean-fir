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
base: a3eca661 on clean local main, including the accepted S18 fixture, generic Nat/Array hotspot batch, lean-zip performance lane, and installed Natural-add heap/heap proof
functional-head: df721ad6, rebased opt-in early finite-target closure lowering; proof request W7-W6-20260823-008 is claimed by W6
contract-base: a3eca661. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed. Closed packages derive module-local closureDispatch and closureDescriptors tables from retained operations; W6 proof adaptation is required before integration
clean-at-update: true
slice: Threaded the final-LCNF pap target set into compileClosureDispatch at the existing closed-package capability. Candidate declarations are filtered once per module; ordinary lower and lowerDecl retain the all-target path. The existing structural pass remains a fail-closed validator. The closed module's exact retained closure operations determine its module-local target and descriptor tables
files: Fir/Wasm/Lower.lean; Fir/Wasm/WellFormed.lean; Fir/Wasm/Emit/Source.lean; Fir/Wasm/Emit/SourceExamples.lean; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: Raw lean-zip retains 734 candidates and avoids constructing 10888 others. Closed metadata is 23 dispatch rows and 38 descriptor rows versus generic 439 and 194. Replacing only those two module-local arrays with the generic post-pass arrays makes the complete symbolic module exactly equal; normalized encoded bytes are exact. Generic opaque ingress is unchanged
performance: Preserving historical all-target metadata erased the optimization and was rejected. One noisy controlled raw run measured generic lowering at 30929ms and finite-target lowering at 18443ms; host load varied heavily, so this is directional evidence only. On the exact current runtime-hotspot base, closure selection reduces plain prettyM from 81997 to 80100 bytes and styled prettyM from 85365 to 83468 bytes, an exact 1897-byte reduction in each module with the same 314 final functions. This is module-size evidence, not a runtime-speed claim
checks: No system /tmp input was used; TMPDIR was the worktree-local .deps/tmp directory. Lean Beam PASS with zero diagnostics for Lower, WellFormed, Source, and SourceExamples. The combined 58-job SourceExamples/ResidentLinker cone PASS. git diff --check PASS. Exact make check PASS: 724 unique cases, 2154/2154 comparisons, 8777 machine steps, 194 active bug cards, all 25 mailbox tests. Complete W7 artifact gate PASS at rebased head ec590f8a: deterministic double generation, checksum/package verification, atomic installation, zero-import resident fixtures, dedicated Nat/Array callers, Node/raw/browser clients, styled trace, stack stress, native/LCNF/V8 differential cone, concrete readiness, scratch/ownership. Plain prettyM is 80100 bytes, SHA-256 503fdfcb1c69986d0ad0b125bd0adfbed6d690c05e950250c1bcf8dd7a0afa1a; styled trace is 83468 bytes, SHA-256 9bd9a8745b2da2cf15e67a28d6ad908d6d8ffc854dd52d159b19c95dea575ce8, with 314 final functions and 24243 origins. The immutable evidence package is integration/talos/artifact/_build/prettyM-current-releases/ec590f8a028e-4b11847619787cb1 and is not a publication pointer. make talos-check passes 3171 of 3172 targets and reports exactly one failure: W6-owned ConcreteClosureDispatch line 450 still states candidatesEq over context.program.decls; every other target, including the accepted installed Natural-add proof, passes
bug-cards: none; no semantic discrepancy was observed
blockers: W6 must adapt ConcreteClosureDispatch.instructions_compileClosureDispatch to the selected declaration array and state the closed-ingress premise. Until that proof compiles and Talos passes, this candidate must not land and dependent prettyM/lean-zip packages must not publish
handoff: The exact current generation input is functional commit df721ad6 on main base a3eca661. W6 owns request W7-W6-20260823-008 and may consume this head directly; integration will validate and land the generation/proof pair atomically
next: W6 selected-declaration closure proof; rerun all Talos jobs; then regenerate prettyM and lean-zip contracts and complete artifact gates as separate W7 consumer commits. Do not add another dependent generator slice to this branch until the closure pair serializes
```
