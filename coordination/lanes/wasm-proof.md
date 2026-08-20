# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c2847c6e on main; accepted W7 direct USize-to-Nat generation stack and all prior scalar contracts
functional-head: e89a77e9
contract-base: W7 Nat.sub functional source 2e9040e0, integrated through c4c9fb4c and present in main base c2847c6e
clean-at-update: true
slice: Closed W7-W6-20260820-004 for W7's direct tagged-pair Nat.sub arm. The new proof module reconstructs the exact private source arm from the public helper, proves FIR-to-Talos adaptation, and retains the complete checked promoted/mixed/arbitrary-limb/stack-safe/malformed branch as an unchanged opaque fallback. Its arithmetic theorem proves unsigned tagged-word order is payload order and that the non-underflow machine expression `leftWord - rightWord + 1` is exactly the canonical encoding of Lean's truncated subtraction; the strict-underflow arm is canonical tagged zero. The operational theorem proves both branches, checked local writes, scratch-memory restoration, caller-tail preservation, and an unchanged concrete store. The final defined-call theorem applies to every related immediate pair and returns `encodeImmediate (left - right)` without allocation.
files: integration/talos/FirTalos/ConcreteResidentNatSub.lean; coordination/lanes/wasm-proof.md
contracts: none changed. The proof consumes the existing ImmediateNaturalPairRel word-order theorems, shared immediate-pair dispatcher, scratch-slot object cast, semantic Wasm ABI, concrete layout, and W7 natSubFunction body. The fallback is adapted exactly rather than duplicated or weakened.
checks: after rebasing on c2847c6e, Lean Beam refresh/sync/save for FirTalos/ConcreteResidentNatSub.lean passed with zero module diagnostics and source hash 358a70cfc9377939; `lake -d integration/talos build FirTalos.ConcreteResidentNatSub` passed (3,079 jobs); `git diff --check main..e89a77e9` passed; `make check` passed (704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713 unique cases, zero findings, 191 active bug cards, 25 mailbox tests); `make talos-setup` passed at Talos 0e05edbc; post-rebase `make talos-check` passed (3,165 jobs).
bug-cards: none
blockers: none. The standalone Nat.sub module is directly compiled and green; the integration owner must add its import to integration/talos/FirTalos.lean because W6 does not own the root umbrella. The rebased branch also retains the preceding green Nat.mul proof and handoff commits d224d04c/026ebcfe, which remain absent from main.
handoff: Integration may validate and fast-forward the three-commit W6 stack d224d04c, 026ebcfe, and functional Nat.sub commit e89a77e9 plus this containing tracked-mailbox commit over c2847c6e. It should add `import FirTalos.ConcreteResidentNatMul` and `import FirTalos.ConcreteResidentNatSub` to the integration-owned Talos umbrella and rerun make talos-check. No W7 implementation, fixture, profile, shared contract, root umbrella, or BOARD file was modified by W6.
next: Consume W7-W6-20260820-011 by proving the direct tagged result of USize.toNat and its exact wide constructor fallback; the general allocating makeNatural theorem remains the next factoring improvement for promoted Nat.mul results.
```
