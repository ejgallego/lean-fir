# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/resident-fast-path-policy
worktree: .worktrees/lean-zip-perf
state: ready
base: adfddcbdc3d0f41759cb4a28efe85bb8915e345e, accepted main including the typed getTag fast path
functional-head: b2989c88c71ec54629cd0eadc59924839cd9b51f
contract-base: adfddcbdc3d0f41759cb4a28efe85bb8915e345e; no shared semantic, ABI, layout, ownership, helper-signature, proof, source-entry, or symbolic-instruction contract change
clean-at-update: true
slice: Make resident caller-fast-path coverage a compile-time policy. Every current Step is exhaustively classified as reviewed out-of-line or inline/cold, with no wildcard. Each inline/cold family carries a proof that its typed rewrite registry is nonempty, so adding a Step or emptying a required provider cannot compile silently. Record compact upstream-aligned object representation as measured, proof-coordinated future work rather than changing the checked 32-byte W6 layout now.
files: Fir/Wasm/Emit/ResidentLinker.lean; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: none. The six existing typed rewrite providers, generated calls, helper bodies and signatures, complete checked fallbacks, concrete representation, import/export surfaces, package layouts, and observable semantics are unchanged. The new policy is a private total classification and erased nonempty witness.
checks: Lean Beam update/sync/save passed Fir/Wasm/Emit/ResidentLinker.lean with zero diagnostics. lake build Fir.Wasm.Emit.ResidentLinker passed all 54 jobs. git diff --check passed. make check passed with 717 native/LCNF cases, 9 direct-machine cases, 717 V8 cases, 2160/2160 comparisons equal, zero findings, and all coverage, bug-card, trusted-assumption, and mailbox policies green. make talos-setup and make talos-check passed all 3172 jobs. bash integration/talos/artifact/check.sh passed deterministic double generation, every resident helper, prettyM stress/package checks, 717-case linked V8 replay, and concrete readiness; prettyM base/trace remained 83904/87318 bytes. bash integration/lean-zip/check.sh passed stored and Level-1 native/Wasm differentials, zero-import adapters, reclamation, deterministic generation, checksums, and smoke. Stored Wasm remained 12418 bytes with SHA-256 3343c2d1c2656c19ceac6c19a6c7cca0162f96e6d28929999f70dba465e6a8f0; Level-1 remained 198424 bytes with SHA-256 107ebbba4d1d431a2dd8f0ac64ec1195e8bfcbb407bca5a95e6772b40c8e24e3.
bug-cards: none
blockers: none
handoff: Fast-forward this clean lane-status commit onto main. The functional code/documentation head is b2989c88c71ec54629cd0eadc59924839cd9b51f. Publication remains local-only; this policy intentionally does not mint or ratchet a package.
next: W6 independently reviews/proves the accepted typed getTag caller branches. New resident Step families must choose an explicit policy and any inline/cold provider must retain a nonempty typed rewrite registry. Revisit compact object representation only when real prettyM and lean-zip profiles justify a coordinated W6/W7 layout milestone.
```
