# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0b942424
functional-head: 355a31da
contract-base: 0b942424
clean-at-update: true
slice: Lifted exact effective named-call kinds through the real declaration-local layout. Production parameter lowering now exposes both exact source-order bindings when all runtime kinds are known and the weaker name-origin fact needed for declarations containing erased/type-level parameters. Declaration hygiene proves parameter/body disjointness; reversal and prefix lookup then yield the exact destination kind in the full compiler context. A supported function exports the resulting getLocal equation directly, without a caller layout certificate or runtime-parameter-totality assumption.
files: Fir/Wasm/Lower.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; coordination/lanes/wasm-proof.md
contracts: proof-facing compiler-local provenance only; production lowering behavior, source semantics, validator acceptance, runtime ABI/layout, symbolic instructions, emitted helpers, ownership, and resident-helper signatures are unchanged
checks: Lean Beam ConcreteReuseCapacityCacheCorrectness update/sync/save (pass, zero errors, source hash a774cfdfce41c8cb); Lean Beam ConcreteFinalLcnfTyping update/sync/save (pass, zero diagnostics, source hash 06aa3e02d8361d6a); lake build Fir.Wasm.Lower (pass: 5 jobs); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3128 jobs); git diff --check (pass); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 7fdead14d647060f7924cae9d8c538bc910950fea515c288c3511bcba9d4542d); make check rerun sequentially after a discarded parallel mutable-build race (pass: scalar artifact 5706 bytes/163 exports, 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation remains confirmed; no new card in this slice
blockers: W6-W7-20260830-003 owns the exact object-case ABI repair; W6-W7-20260830-004 audits real named-call argument/result edges before selecting a directional validator or minimal-provenance policy
handoff: clean W6 functional head `355a31da`, based exactly on accepted main `0b942424`; ready for fast-forward integration
next: Package the exact-local theorem as an internally constructed and source-step-preserved current-code invariant, then discharge DirectInternalCallCompilerAdmission.resultCompiled. The two directional named-call edges remain with W6-W7-20260830-004.
```
