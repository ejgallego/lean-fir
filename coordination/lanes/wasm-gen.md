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
base: 8a0e467f40badd48da0f267eb8efb4f7d3fef814, accepted main containing the seven-family scalar-boxing source frontier and aligned W6 structured-validation checkpoint
functional-head: 1697038a132ef1b138a194336252d7625c66a6aa
contract-base: 8a8d138734d0a9e2d9373db7f9629bade0b79ff2; W7 consumes the accepted heap-only floating semantic representation and concrete executable-host marker inventory without claiming a W6 helper refinement theorem or changing the allocator, ownership policy, source semantics, or symbolic Wasm instruction surface
clean-at-update: true
slice: Internalize generic heap-only, bit-exact `Float32` box/unbox helpers and align the floating marker inventory to `Float32 = 6`, `Float = 7`. Both helpers validate canonical 40-byte owned boxes; the Float32 payload occupies four bytes with zero high padding. Integer-lane standalone façades preserve signed zero, subnormals, infinities, and quiet/signaling NaN payloads without JavaScript numeric conversion. Flip the existing Float32 generic and compiler-generated `_boxed` source fixtures to a zero-import, zero-runtime-operation ratchet.
files: Fir/Wasm/Emit/ResidentFloat.lean; Fir/Wasm/Emit/ScalarBoxingExamples.lean; Fir/Wasm/Emit/SCALAR_BOXING_CONFORMANCE.md; integration/talos/artifact/resident-float-client.mjs; integration/talos/artifact/README.md; bugs/FIR-BUG-wasm-none-float32-resident-boxing.md; coordination/lanes/wasm-gen.md
contracts: executable W7 helpers now use the already accepted floating semantic representation and concrete-host scalar marker inventory. Helper names are `fir_float32_box`, `fir_float32_unbox`, `fir_float_box`, and `fir_float_unbox`; a separate W6 checkpoint must promote and prove this stable executable layout. No theorem, source semantic, symbolic Wasm, allocator, or ownership contract changed.
checks: Lean Beam sync/save passed ResidentFloat and ScalarBoxingExamples with zero diagnostics. Focused `lake build Fir.Wasm.Emit.ScalarBoxingExamples` passed 55 jobs; the artifact dependency cone passed 95 jobs. git diff --check passed. make check passed with 719 source cases, 9 direct-machine cases, 728 unique cases, and 2166/2166 comparisons equal. make talos-setup completed and make talos-check passed all 3174 jobs. bash integration/talos/artifact/check.sh passed every resident helper, both complete prettyM packages, the full 719-case validation cone, and concrete readiness. A separate two-emission check compared the resident-Float Wasm and manifest byte-for-byte.
evidence: the resident-Float module is 7248 bytes with SHA-256 fa806f59e3c1c0e56d52a6fe35fb5a3a5496f7e09b7183084b2a13af697a6c58; its 1573-byte manifest has SHA-256 94926697892f084f9c2425130f239e8d1bb20ae1f102db676376e3ee7c5ba1ac. It owns memory, has zero imports, exposes the four floating helpers plus the checked standalone probes, grows exactly 40 bytes per box, and rewinds to the prior frontier. Six of seven scalar families now close to zero imports and zero runtime operations; the unresolved-family guard is exactly #["USize"]. The complete artifact gate selected immutable package _build/prettyM-current-releases/2f6c3ef1fb30-df2c31c09b070106; plain and styled Wasm sizes remain 83982 and 87396 bytes.
bug-cards: FIR-BUG-wasm-none-float32-resident-boxing fixed on the generation side; W6 proof promotion remains explicit follow-up
blockers: none for Float32 generation readiness. USize is the only remaining scalar-family generation frontier and depends on the shared target-width contract stack.
handoff: Fast-forward the clean containing status commit onto main. Functional head 1697038a132ef1b138a194336252d7625c66a6aa is based on accepted main 8a0e467f40badd48da0f267eb8efb4f7d3fef814. This is runtime infrastructure and does not advance a canonical consumer package pointer.
next: Queue W6 promotion/refinement of the stable floating box descriptor, land the USize contract stack when its LCNF/W6 adaptations are ready, then add the all-fourteen-entry external-engine ratchet.
```
