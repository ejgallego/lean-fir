# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 6910495c, current main after accepted checked-decrement gates
functional-head: 10d5b4d9
contract-base: 6910495c; W7's complete validateNatural body and the resident validateCommon/naturalLow/naturalHigh helper signatures are consumed unchanged
clean-at-update: true
slice: Proved that W7's exact installed validateNatural function terminates successfully for every canonical W6 heap-Natural admission. `terminatesWith_validateNatural_of_naturalAdmission` derives the complete generated body adaptation and execution: common header/extent validation, Natural kind and big-marker dispatch, ordinary-or-persistent ownership, zero reserved fields, exact top low/high helper calls, nonzero canonical top limb, and the one-limb promoted-boundary guard. The target store, caller operand tail, and trace are unchanged. Supporting W6 abstractions expose the canonical top limb and one-limb high-word fact once, while reusable Talos guard WPs and `NaturalValidationCalls` factor the helper graph without certificates or trusted caller premises.
files: Fir/Wasm/Concrete/NaturalAllocationCorrectness.lean; integration/talos/FirTalos/ConcreteResidentBigNumeric.lean; bugs/FIR-BUG-wasm-none-natural-validator-refinement-admission.md; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, resident helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. `NaturalValidatorAdmission`, its canonical-limb consequences, the proof-side exact program spelling, call bundle, and guard WPs are W6 proof surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for NaturalAllocationCorrectness.lean (source hash c2bf8332ce154f18) and ConcreteResidentBigNumeric.lean (source hash 5340730393ce6193). Focused `lake build FirTalos.ConcreteResidentBigNumeric` passed 3,075 jobs. The four-commit W6 stack rebased without conflict from ff295018 onto current main 6910495c. On rebased functional head 10d5b4d9, `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 193 active bug cards, 25 mailbox tests, and all 3,171 Talos jobs. Talos is pinned at 0e05edbc.
bug-cards: FIR-BUG-wasm-none-natural-validator-refinement-admission records the still-open mismatch between broad LiveCellRel.natural admission and the canonical representation accepted by validateNatural
blockers: none for landing this canonical-validator checkpoint; the public checked Nat.add theorem still cannot derive NaturalValidatorAdmission directly from the broader LiveHeapRel/LiveCellRel.natural relation
handoff: Integration may fast-forward the accepted stack through W6 functional head 10d5b4d9 and this containing status commit. W7 may consume the installed canonical-validator theorem without supplying header loads, ownership/reserved-field checks, top-limb reads, helper-call behavior, store preservation, caller-tail preservation, or trace-freedom premises.
next: Prove and preserve the compiler-facing bridge from the heap/value simulation relation to NaturalValidatorAdmission (or strengthen the Natural cell relation at the canonical allocation boundary), then compose validator success with the existing checked prefix, result-count split, and generated multi-limb producer to state the public heap/heap Nat.add typed-result theorem. Cover promoted-tag admission as a separate representation arm rather than weakening the canonical big-Natural theorem.
```
