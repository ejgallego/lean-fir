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
base: 3531014a on clean local main, including the accepted selected-closure generation/proof pair, typed Nat call-site registry and fast paths, S19 mutual-tail ownership fidelity, public production decrement proof surface, and durable rejected increment experiment
functional-head: 0f351de8, exposing the exact production decrementOnceFunction to W6 without changing its body; accepted typed call-site implementation 72eaf6f and selected-closure implementation df721ad6 remain the current generated-code heads
contract-base: 3531014a. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed. Every call-site rewrite is registered with its exact semantic FIR signature. Closed packages retain finite source target sets; generic ingress retains every declaration. The production decrement helper is definitionally visible to W6 and otherwise unchanged
clean-at-update: true
slice: Accepted the mandatory semantic-signature registry for resident call-site rewrites plus tagged Nat.decLt, saturating Nat.sub, and nonoverflowing Nat.mul caller branches. Heap, mixed, and overflow paths retain complete helpers. Exposed production decrementOnceFunction itself for the active W6 release proof. Integrated the contract-neutral S19 mutual-tail fixture. Retained negative results for Nat.decLe and checked increment factoring; both emitter candidates were discarded
files: Fir/Wasm/Emit/ResidentCallSite.lean; Fir/Wasm/Emit/ResidentBigNumeric.lean; Fir/Wasm/Emit/ResidentNatArithmetic.lean; Fir/Wasm/Emit/ResidentRelease.lean; focused resident linker clients; integration/lean-zip package contract and evidence; Fir/Validation/Corpus.lean; validation plans; coordination lane and board records
contracts: Typed caller rewrites fail closed on missing, duplicate, or signature-incompatible registrations, and final symbolic validation still checks replacement bodies at actual caller stack boundaries. The Nat helpers, resident decrement helper, layout, ABI, ownership, and arbitrary-precision fallbacks are unchanged. S19 adds observations and telemetry only
performance: The accepted typed-Nat batch improves the balanced level-6 median from 64.12ms to 52.55ms, about 18%, with 8/8 pairs improving; module size grows from 454918 to 478669 bytes. Nat.decLe was neutral at 45.24ms versus 45.36ms and was rejected. Checked increment factoring shrank the candidate module from 478669 to 414781 bytes but was neutral at 40.77ms versus 40.70ms with a +0.05ms paired median and 16/32 wins, so its emitter change was discarded under the runtime policy
checks: No system /tmp input was used; TMPDIR was worktree-local. The accepted typed-Nat batch passed Lean Beam, the ResidentLinker cone, make check, all 3172 Talos jobs, and the complete deterministic W7 artifact gate. The production decrement proof surface passed Lean Beam update/sync/save with zero diagnostics and source hash 02eaedeee0f8329e, the 54-job emitter/linker cone, make check at 725 unique cases and 2157/2157 comparisons with 8959 machine steps, and all 3172 Talos jobs. S19 independently passed its focused nine-edge native/LCNF/V8 gate and the same complete repository/Talos boundary. Both rejected experiments preserved exact output and flat post-rewind frontiers
bug-cards: FIR-BUG-wasm-none-selected-lowering-proof-surface is fixed; active W6 release proof records FIR-BUG-wasm-none-liveheaprel-canonical-header-words; no new W7 discrepancy
blockers: none
handoff: Current accepted local main is 3531014a. W7 proof-surface head 0f351de8 is available to W6 through operational update W7-W6-20260825-002. The checked-increment lease completed with disposition decided and no emitter change
next: Regenerate and atomically publish exact prettyM and lean-zip packages from accepted main as separate consumer ratchets. Then prioritize proof convergence for release, typed Nat, and trusted Array paths before admitting another unprofiled caller rewrite; the next performance investigation is lzMatchP ownership traffic
```
