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
base: cf3f7cb8 on clean local main, including the accepted generation/proof stack and convergence-board checkpoint
functional-head: 9813e9c8, ratcheting the stored, Level-1, and raw lean-zip consumers after deterministic regeneration; production proof-surface head 0f351de8 remains available to W6
contract-base: cf3f7cb8. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed
clean-at-update: true
slice: Published exact clean-current prettyM and lean-zip packages after accepting the typed Nat caller branches, public production decrement helper, S19 mutual-tail fixture, and rejected checked-increment evidence. The consumer ratchets preserve reviewed closure inventories and zero-import contracts
files: Fir/Wasm/Emit/ResidentCallSite.lean; Fir/Wasm/Emit/ResidentBigNumeric.lean; Fir/Wasm/Emit/ResidentNatArithmetic.lean; Fir/Wasm/Emit/ResidentRelease.lean; integration/talos/artifact package publication; integration/lean-zip package contracts and publication; Fir/Validation/Corpus.lean; validation plans; coordination lane and board records
contracts: Typed caller rewrites fail closed on missing, duplicate, or signature-incompatible registrations, and final symbolic validation still checks replacement bodies at actual caller stack boundaries. The Nat helpers, resident decrement helper, layout, ABI, ownership, and arbitrary-precision fallbacks are unchanged. S19 adds observations and telemetry only
performance: The accepted typed-Nat batch improves the balanced level-6 median from 64.12ms to 52.55ms, about 18%, with 8/8 pairs improving; module size grows from 454918 to 478669 bytes. Nat.decLe was neutral at 45.24ms versus 45.36ms and was rejected. Checked increment factoring shrank the candidate module from 478669 to 414781 bytes but was neutral at 40.77ms versus 40.70ms with a +0.05ms paired median and 16/32 wins, so its emitter change was discarded under the runtime policy
checks: No system /tmp input was used; TMPDIR was worktree-local. The accepted implementation and proof-surface stack passed Lean Beam, focused dependency cones, make check at 725 unique cases and 2157/2157 comparisons with 8959 machine steps, all 3172 Talos jobs, and the complete deterministic W7 artifact gate. prettyM passed deterministic double generation, checksums, and smoke. Stored, Level-1, and raw lean-zip passed deterministic double generation, native/Wasm differentials, cache/scratch ownership checks, zero-import assertions, checksums, Node smoke, and Chrome execution
bug-cards: FIR-BUG-wasm-none-selected-lowering-proof-surface is fixed; active W6 release proof records FIR-BUG-wasm-none-liveheaprel-canonical-header-words; no new W7 discrepancy
blockers: none
handoff: Consumer head 9813e9c8 is ready above accepted main cf3f7cb8. prettyM release is _build/prettyM-current-releases/cf3f7cb88506-c0daf337cf9654f2 (83996 bytes; fc61301d946b1596ad08c9b20d51d2e1f68d60ca0c04b0f9d56e298c2ec6408d). Stored lean-zip is _build/lean-zip-stored-packages/9813e9c82dd7-273d0d6cd9ca-672ecf6a86ee22473a3b (12678 bytes; ea2172a2fcce26cdc292deb9a97fc70789bb85786dace69864e838877096052a). Level-1 is _build/lean-zip-level1-packages/9813e9c82dd7-273d0d6cd9ca-f2352d2aeae0be229f92 (195273 bytes; b124270a8b38e4f43d85df08a3e4970d6c8b94e5b5b86f3a8f39f591693260e7). Raw is _build/lean-zip-raw-packages/9813e9c82dd7-273d0d6cd9ca-88a4507a2bb77a8c17d0 (414753 bytes; 3623bb8496127bb9115cdef57949019a268432d4f9c4ca7344e425e3944e84ed). All are module-memory and zero-import packages
next: Prioritize proof convergence for production release, typed Nat, and trusted Array paths before admitting another unprofiled caller rewrite. FIX-W7-20260825-003 is the next independent fidelity integration; the next performance investigation remains lzMatchP ownership traffic
```
