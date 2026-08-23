# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d124340e, current main after the independent Verso HTML package refresh
functional-head: 681190e3
contract-base: d124340e; the current W7 checked-Nat body and resident allocator/count/low/high/writer helper signatures are consumed unchanged
clean-at-update: true
slice: Closed the exact generated checked multi-limb Natural-result producer over two checked heap operands. `NaturalSumWriterInstallation.wp_checkedMultiLimbResultProgram_of_operandViews` composes the installed resident allocator and full count/low/high/magnitude/writer graph, the exact padded-limb arithmetic, optional carry stores, W6 heap/witness extension, preserved `ResidentMemoryRel`, exact `ValueRel` for `leftValue + rightValue`, and the typed Talos WP for `checkedMultiLimbResultProgram`. Both carry branches are derived internally. All eight intermediate scratch writes are constructed from one stable `initial.validIndex 17` fact, and the carry-store bounds come from the exact allocation/prefix proof rather than caller assumptions.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, resident helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. The installation/composition bundles are proof-side W6 surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash a001d11447a4a5bf). Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,122 jobs. The 35-commit W6 stack rebased without conflict from a2ef2d42 onto current main d124340e; the intervening commits only refresh the Verso HTML package. On rebased functional head 681190e3, `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,171 Talos jobs. Talos is pinned at 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this generated-producer checkpoint; checked heap/heap Nat.add now has a typed WP for the actual generated multi-limb result program from the real installed helper graph
handoff: Integration may fast-forward the accepted stack through W6 functional head 681190e3 and this containing status commit. W7 may consume the generated-producer theorem without supplying trusted allocation, helper-call, arithmetic, carry, direct-store bounds, scratch-local updates, heap-extension, or result-typing premises.
next: Connect the generated producer theorem to the surrounding public `natAdd` checked prefix and result-count split, reusing the existing checked operand admission/count/carry theorems; then state the public function-level typed heap/heap result theorem.
```
