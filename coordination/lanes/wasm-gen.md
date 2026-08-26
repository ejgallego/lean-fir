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
base: d579ae2d9ff0bb375203b869da88a2e2867c85ce, accepted main including the W6 promoted/tagged decrement proof stack
functional-head: e215b90bae7252c6455aaa40cb01714c479b68ba
contract-base: d579ae2d9ff0bb375203b869da88a2e2867c85ce; no shared semantic, ABI, layout, ownership, helper-signature, proof, source-entry, or symbolic-instruction contract change
clean-at-update: true
slice: Apply upstream-shaped checked decrement gates inside resident Array, ByteArray, Nat, and String callers. Tagged values and erased zero stay in the caller; only heap references enter fir_dec_once. Typed heap-only object values retain their direct decrement path. The stable helper body remains byte-for-byte unchanged, so the W6 proof stack lands first and remains the proof boundary.
files: Fir/Wasm/Emit/ResidentRelease.lean; Fir/Wasm/Emit/ResidentArray.lean; Fir/Wasm/Emit/ResidentByteArray.lean; Fir/Wasm/Emit/ResidentNatArithmetic.lean; Fir/Wasm/Emit/ResidentString.lean; Fir/Wasm/Emit/ROADMAP.md; integration/lean-zip/README.md; integration/lean-zip/closure-contract.json; integration/lean-zip/level1-closure-contract.json; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: none. fir_dec_once retains its name, signature, locals, recursive body, validation/trap policy, layout, ABI, and installation order. Generated caller bodies and deterministic artifact identities change; source semantics, imports/exports, ownership frontier, and heap-reference decrement behavior do not.
checks: Lean Beam sync/save passed ResidentRelease, ResidentArray, ResidentByteArray, ResidentNatArithmetic, and ResidentString with zero diagnostics. The focused 27-job emitter build passed. git diff --check passed. make check passed on the rebased head with 726 unique cases, 2160/2160 comparisons equal, zero findings, and all policies green. make talos-setup selected Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254 and make talos-check passed all 3172 jobs. bash integration/talos/artifact/check.sh passed deterministic generation, every resident helper, prettyM stress/package checks, the 717-case V8 cone, and concrete readiness. bash integration/lean-zip/check.sh passed deterministic double generation, native/Wasm stored and Level-1 differentials, zero-import adapters, scratch/cache reclamation, checksums, and package smokes. The separate raw source-closure deterministic preview and 5x10-level differential passed. No browser executable was configured for the Talos gate.
evidence: One steady 256-KiB seeded-random level-6 call reduces fir_dec_once entries from 1222005 to 169608 (-86.1%) and tagged no-op entries from 1195723 to 143326 (-88.0%), while all heap categories remain exact. Sixteen unprofiled order-balanced AB/BA rounds improve 16/16: median 33.097129 to 30.978935 ms/call, paired median -2.096125 ms (-6.3834%). fir_dec_once profile self share falls from 4.161% to 1.812%. Raw Wasm is 367634 bytes, SHA-256 36be5cfbcf823a89375bfcb617b0b85d295d8a6f0df6afdeac0228424ea1efab; stored is 12444 bytes, SHA-256 1eb22ee7da340d2b6d4878892c82554efadb6c26cd57307cf7dc52279d929492; Level-1 is 199468 bytes, SHA-256 872b7b8473d6c2ea463bc6cb299d7ceed5606d5d34663baa67280969294ba9e8. All have zero imports.
bug-cards: none
blockers: none
handoff: Fast-forward this clean lane-status commit onto main after resolving the containing status head from wasm/generation. The functional code/documentation head is e215b90bae7252c6455aaa40cb01714c479b68ba and is based directly on the already-landed W6 decrement proof stack. Publication remains local-only; this slice ratchets reproducible package bytes but does not advance an external canonical pointer.
next: W6 may separately connect the new checkedDecrementLocal caller gate and resident call sites to the existing concrete decrement theorem; this does not block generation readiness. The remaining 143326 tagged entries originate chiefly inside recursive generic release and would require a proof-coordinated helper-body change, so do not overlap that work with the active UInt64 boxing slice.
```
