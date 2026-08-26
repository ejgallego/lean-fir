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
base: 1fade2aadbea8293354a5fef8f86022b28b660cd, accepted main after the consolidated W7 integration stack and bounded Nat/USize package ratchets
functional-head: a77e9760cccd505a2b4612fad2aed8a533b93d2c
contract-base: 1fade2aadbea8293354a5fef8f86022b28b660cd; no shared semantic, helper-signature, layout, ownership, or W6 proof contract changed
clean-at-update: true
slice: Repairs generic resident internalization when a reviewed call-site rewrite introduces memory instructions and the selected helper installs module-owned memory. The transaction now validates the untouched input, rewrites callers, installs the helper and memory as one unchecked intermediate, and validates the completed output. A focused memoryless getTag regression preserves invalid-input checking and requires the import-free result to validate and encode. The exhaustive prettyM clients were also ratcheted to the bounded-Nat import frontier already present on main.
files: Fir/Wasm/Emit/ResidentRuntime.lean; bugs/FIR-BUG-wasm-none-callsite-memory-installation-order.md; integration/talos/artifact/resident-numeric-client.mjs; integration/talos/artifact/resident-big-numeric-client.mjs; integration/talos/artifact/resident-string-client.mjs; and this lane status
contracts: none. Resident helper bodies and signatures, semantic Wasm ABI, concrete layout, memory ownership, and W6 theorem statements are unchanged; only W7 transaction ordering and exact intermediate acceptance counts changed.
checks: Lean Beam update/sync/save on Fir/Wasm/Emit/ResidentRuntime.lean passed with zero diagnostics; focused lake build Fir.Wasm.Emit.ResidentRuntime Fir.Wasm.Emit.ResidentPrettyFormat passed 57 jobs; FIR_PRETTYM_CHECKPOINTS=1 source generation passed; git diff --check passed; make check passed 730 unique cases, 2172/2172 comparisons, 721-case native/LCNF/V8 triangle, coverage policy, 211 bug cards, trusted-source validation, and 38 mailbox tests; make talos-setup plus make talos-check passed all 3174 jobs with exact receipt 59b635e38c1cc444cf367205942e38e7c3bda1e99bba8933e8a60b03da8dfba4; FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 integration/talos/artifact/check.sh passed every intermediate checkpoint, final zero-import package, adapter/package determinism, shared validation, and 44/44 concrete readiness artifacts.
evidence: generic linker fix 8901da83a87d117a36c970e96450db9220e1506f; exact exhaustive frontier ratchets a77e9760cccd505a2b4612fad2aed8a533b93d2c; final prettyM module 87396 bytes with 322 functions and 25493 instruction-origin records; exhaustive import progression ends 13 -> 1 -> 0 after numeric, String, and panic internalization.
bug-cards: FIR-BUG-wasm-none-callsite-memory-installation-order fixed with in-module regression
blockers: none
handoff: Integrate the containing clean status checkpoint after verifying it descends from base 1fade2aa. Integration remains owned by fir/root; no W6 adaptation is required.
next: After integration, tooling may rebase its source-isolation work and rerun the exhaustive gate. W7 returns to the consumer-driven generation queue.
```
