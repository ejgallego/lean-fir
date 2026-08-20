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
base: 1b8a5a11 on main
functional-head: 65f4a57c, preserve native final-LCNF source-unit boundaries and migrate HitScene production to the repaired hybrid capture
contract-base: 1b8a5a11. No Lean semantic, semantic Wasm ABI, resident-helper signature, symbolic-module, or W6 proof contract changed. The generic source capture now respects the source units made available by Lean's final compiler pipeline
clean-at-update: true
slice: compileEntryIndividuallyInternalized now replays a postponed public entry's exact module-owned final-LCNF groups before compiling recursively discovered ordinary imported roots as separate final-pass-captured units. Every individual root uses exact final-impure capture rather than stale environment recovery, and the merged graph is reachability-pruned before Wasm admission. HitScene production uses this generic hybrid path; its former grouped-dependency path remains diagnostic only. The generic postponed-source-view builder unlinks its exact read-only Lean outputs before repeat builds, with a direct deterministic rebuild regression
files: Fir/Wasm/Emit/Source.lean; Fir/Wasm/Emit/SourceExamples.lean; bugs/FIR-BUG-wasm-none-individual-hit-scene-generated-helper-admission.md; integration/illuminate-hit-scene/IlluminateFirHitScene/Compile.lean; integration/illuminate-hit-scene/ProbeIndividual.lean; integration/illuminate-hit-scene/README.md; integration/illuminate-hit-scene/closure-contract.json; integration/illuminate-hit-scene/illuminate-hit-scene-browser-adapter.mjs; integration/illuminate-hit-scene/package-smoke.mjs; integration/illuminate-hit-scene/package.mjs; integration/package-tools/postponed-source-view.mjs; integration/package-tools/postponed-source-view.test.mjs; coordination/lanes/wasm-gen.md
contracts: HitScene BUILD schema v2 now records 313 reachable declarations, 53 reviewed externals, 261 base functions, 774 frontier functions, the exact pre-link Float.cos/Float.sin/Float.atan2/Float.acos/Float.cbrt order, zero final imports, six function exports plus memory, and module-owned memory. Public query, diagnostic query, bit-exact coordinate transport, persistent checkpoint, copied output, scratch rewind, disposal, and fir.standard-libm/v2 contracts are unchanged
artifacts: clean functional producer 65f4a57c and clean Illuminate 88dcfee895a5. Immutable package integration/illuminate-hit-scene/_build/illuminate-hit-scene-8c890b70828ec3b2 is 64217 bytes at SHA-256 0a59717fef0dafb2fac65e0cbc44c39b5116ab5bd30796be4b1853e1e25d7480, package SHA-256 8c890b70828ec3b2e426251b2a7049ce00896d9d7cf17332bcfd33ce90ca28c5, canonical pointer illuminate-hit-scene-current. Base module is 51719 bytes at 4519093eae75f5da027d8fd31d5505ca2e823d768abbbc276a491db7d7eacc13; pre-libm frontier is 106992 bytes at 2b26d8e3f42cf37675c210124e094f1500af55786fa4392b6645f3b3ee1c721d
checks: All scratch paths were worktree-local under ignored .deps storage; system temporary storage was not used. Lean Beam update/sync/save PASS for edited Lean modules. lake build Fir.Wasm.Emit.SourceExamples PASS; lake build IlluminateFirHitScene.Compile PASS. ProbeIndividual PASS with 313 declarations, 53 externals, 261 functions, zero unsupported declarations, supported admission, and successful lowering. Production Probe PASS with the same source inventory. Postponed-source-view tests PASS 3/3 including a read-only repeat rebuild. HitScene package PASS 301 fixture queries and 10000 flat-frontier queries, deterministic repeat generation/link, zero imports, exact exports, and complete SHA256SUMS. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 189 active bug cards. make talos-setup PASS; make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including package tools, deterministic source-Float/libm/resident/prettyM checks, 704 native/LCNF/V8 cases with 2112 comparisons, all 44 concrete artifacts, and all 15 source probes
bug-cards: FIR-BUG-wasm-none-individual-hit-scene-generated-helper-admission (fixed by the generic source-boundary repair; no admission weakening or declaration-specific shim)
blockers: none
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 65f4a57c is based directly on 1b8a5a11. No W6-owned file or shared semantic contract changed and no external package publication is authorized
follow-up: Review additional consumers before migrating them: SpatialHitScene uses a multi-entry synthetic capture path and was intentionally not changed by this slice. Measure the higher source-capture cost separately from runtime performance; the complete HitScene module nevertheless shrank by 3339 bytes
```
