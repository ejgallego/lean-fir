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
base: 0e836ad5c4f636f2a2cd2fda41c4472427079bc6, accepted main containing heap-only USize convergence, sampled-profile contract v1, and the integration-lease handoff to fir/root
functional-head: 9c896a1d2ba7b9559040ef9a0fab6a8d61cdc273
contract-base: 1db0b79d4b1607ee311432a27b5460853300399a; consumes the isolated heap-only USize semantic contract while retaining the existing semantic ABI signature, scalar-box layout, allocator, marker, and ownership contract
clean-at-update: true
slice: W7-1 is resumed at a clean generation checkpoint after relinquishing the dynamic integration lease. The last functional slice internalizes heap-only USize box/unbox through the generic resident scalar-box layer; every payload allocates the existing 40-byte owned object and tagged USize unboxing traps. No new generator/runtime change is active. The current canonical catalog already covers prettyM, retained Illuminate player and query packages, Verso Flat/HTML, and zero-import lean-zip.
files: coordination/lanes/wasm-gen.md only for this status refresh; the last functional files remain Fir/Wasm/Emit/ResidentScalarBox.lean, Fir/Wasm/Emit/ScalarBoxingExamples.lean, integration/talos/artifact/README.md, and integration/talos/artifact/resident-scalar-box-client.mjs
contracts: no new shared contract. The accepted heap-only USize semantic ABI, helper signatures, concrete layout, allocator, markers, ownership rules, symbolic Wasm surface, public exports, and unrelated scalar policies remain unchanged.
checks: the accepted functional stack passed Lean Beam, focused LCNF/W6 cones, make check with 730 unique cases and 2172/2172 comparisons, all 3174 Talos jobs, and the complete deterministic artifact/concrete/V8 gate. The subsequent rebase adds only accepted tooling and coordination commits; this status refresh passes git diff --check and mailbox validation.
evidence: the seven-family source boxing ratchet is closed with zero imports and zero residual runtime operations. Roadmap audit finds no real-source closure currently blocked on a missing W7 runtime family. Generation-ready caller/release items already have independent W6 proof requests; bounded Nat.land and USize range-fact successors belong to W7-2; check-throughput belongs to tooling.
bug-cards: FIR-BUG-impure-none-usize-box-tagged fixed
blockers: none in the compiler. Shared SOURCE_PACKAGE publication remains intentionally deferred until Illuminate completes the third consumer review; no client has supplied a new unsupported source closure.
handoff: W7-1 is clean on accepted main 0e836ad5. Integration is owned by fir/root; W7-1 will not land W7-2, tooling, W6, or LCNF checkpoints.
next: Stay checkpointed until either Illuminate returns the SOURCE_PACKAGE review or a real source closure exposes a missing generic compiler/runtime capability. Do not preemptively implement fail-closed FloatArray/DataArray/DOM/callback or other unused families, and do not overlap W7-2's Nat.land/USize fact work.
```
