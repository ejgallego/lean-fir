# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a2ef2d42, current main after trusted ByteArray and tooling-profile integration
functional-head: 0108f294
contract-base: a2ef2d42; the current W7 checked-Nat body and resident count/low/high helper signatures are consumed unchanged
clean-at-update: true
slice: Closed the next checked heap/heap Natural-add composition layer. `NaturalObjectAllocatorInstallation` packages the real resident allocator call. `NaturalSumWriterInstallation.terminatesWith_after_allocateObject` composes its exact successor store with checked operand views and the installed count/low/high writer graph. `typedResult_of_operandViewWriterRun` then converts one exact writer run into a final W6 heap/witness, preserved `ResidentMemoryRel`, and exact `ValueRel` for `leftValue + rightValue`, including noncanonical leading-zero input limbs and the optional final carry limb. The supporting pure theorem proves the completed padded result words denote the mathematical sum and that the writer carry is exactly zero or one.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, resident helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. The installation/composition bundles are proof-side W6 surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash 6591909b70ceeca1). Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,122 jobs. On functional head 0108f294, `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,171 Talos jobs. Talos is pinned at 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this useful semantic checkpoint; checked heap/heap Nat.add now reaches a typed exact sum result from the real installed allocator and writer graph
handoff: Integration may fast-forward the accepted stack through W6 functional head 0108f294 and this containing status commit. W7 may consume the typed writer-result theorem instead of supplying trusted allocation, helper-call, arithmetic, carry, heap-extension, or result-typing premises.
next: Wrap the exact allocator/writer calls with the generated `checkedMultiLimbResultProgram` local-control and carry branch, then connect that generated producer theorem to the public checked `natAdd` branch.
```
