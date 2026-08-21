# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 19b9725b
functional-head: 7e1a47fb
contract-base: current main 19b9725b; transparent impure-hygiene work is separately claimed in W6-W7-20260820-021 and remains isolated
clean-at-update: true
slice: Factored the scratch-free direct-result boundary needed by W7's pending Nat.add change. The symbolic uint64-to-tobject sequence adapts exactly to Talos unsigned-extend/wrap, while a separate physical theorem proves every i32 word, the full store and memory, and the caller operand tail are unchanged. The theorem deliberately claims no object validity for an arbitrary word; the later Nat.add specialization must retain the naturalSum tagged-or-live-heap witness. The existing Nat-decision proof now consumes the common physical lemma instead of duplicating its bit-round-trip argument.
files: integration/talos/FirTalos/ConcreteResidentPrimitives.lean; integration/talos/FirTalos/ConcreteResidentNatDecision.lean; coordination/lanes/wasm-proof.md
contracts: none changed. This is a proof-only factoring over the existing symbolic instructions, Talos adapter, and Wasm execution semantics. No emitter, ABI, layout, helper signature, ownership behavior, or validity premise changed.
checks: Lean Beam sync/save passed with zero diagnostics for ConcreteResidentPrimitives.lean (source hash 376677875ce29c96) and ConcreteResidentNatDecision.lean (source hash 71c399f3d240104a). `lake -d integration/talos build FirTalos.ConcreteResidentNatDecision` passed (3,079 jobs). `git diff --check` passed. `make check` passed (713 unique cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests). `make talos-setup` refreshed Talos 0e05edbc. `make talos-check` passed (3,167 jobs). `make mailbox-check` passed (68 threads, 236 messages).
bug-cards: none
blockers: none for this ready primitive; the function-specific Nat.add specialization waits for W7 to return the exact rebased generation, ratchet, and tracked heads in W7-W6-20260820-015
handoff: Integration may land functional commit 7e1a47fb plus this containing status commit on main 19b9725b independently of the still-unrebased W7 Nat.add body. Operational update W6-W7-20260820-027 records the prepared boundary and retained validity obligation.
next: Rebase onto W7's exact direct-result Nat.add generation head, replace the stale scratch shape with typedObjectWordRoundTripSource/unsignedI32RoundTrip, specialize the physical theorem to naturalSum's exact related result for tagged and promoted heap Naturals, retain the checked fallback, and land generation plus proof atomically.
```
