# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a2ef2d42, current main after trusted ByteArray and tooling-profile integration
functional-head: 692ff3a1
contract-base: a2ef2d42; the current W7 checked-Nat body and resident count/low/high helper signatures are consumed unchanged
clean-at-update: true
slice: Connected checked physical Natural operands to the installed multi-limb sum writer. A successful W6 decoder now exposes an exact arbitrary-index limb list/value view. The Talos side packages static count/low/high installation facts separately from evolving store evidence, frames arbitrary operand loads across every fresh-result prefix, and proves magnitude dispatch returns exactly the corresponding padded limb word (including exact zero beyond an operand's own count). `NaturalSumWriterInstallation.terminatesWith_of_operandViews` instantiates all four writer callbacks from two checked views and derives every result-store bounds check from the allocation/frontier relation. The resulting theorem returns the exact pure `addLimbWords` prefix and carry without trusted helper-call premises.
files: Fir/Wasm/Concrete/NaturalAllocationCorrectness.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, resident helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. `NaturalLimbView` and the installation bundles are proof-side W6 composition surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for NaturalAllocationCorrectness.lean (source hash 4404f9d660ebcf72) and ConcreteResidentNat.lean (24b09abec1a0d156). Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,122 jobs before the no-conflict rebase. On rebased head 692ff3a1, `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,171 Talos jobs. Talos is pinned at 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this useful writer-composition checkpoint; checked heap/heap Nat.add now reaches an exact written result prefix and carry from the real installed helper graph
handoff: Integration may fast-forward the accepted stack through W6 functional head 692ff3a1 and this containing status commit. W7 may rely on the installed writer theorem for two checked heap Natural views rather than supplying trusted count, limb, magnitude, evolving-store frame, or result-bounds premises.
next: Compose the existing checked raw allocator run with `NaturalSumWriterInstallation.terminatesWith_of_operandViews`, materialize the optional carry limb, and close the result through the existing decoder/live-heap theorem to obtain the typed checked heap/heap Nat.add result theorem.
```
