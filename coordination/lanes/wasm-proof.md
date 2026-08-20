# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f8c1069d on main; accepted direct-USize generation/proof stack and W7 tagged-pair Nat.mul implementation
functional-head: 0dcef319
contract-base: W7 functional source 0811a912, integrated through 4fea3692 and present in main base f8c1069d
clean-at-update: true
slice: Closed W7-W6-20260820-003 for W7's direct tagged-pair Nat.mul arm. The new proof module recovers the exact private source arm from the public helper, proves FIR-to-Talos adaptation, and preserves the complete validator-first promoted/mixed/arbitrary-limb/malformed checked branch as the unchanged opaque fallback. Its operational theorem proves both payload decodes, non-wrapping 31-bit-by-31-bit i64 multiplication, exact low/high constructor arguments, checked local writes, restoring scratch cast, caller-tail preservation, and the constructor's exact store transition. The general theorem therefore composes with either a tagged or heap-extending promoted constructor outcome; a closed corollary proves the product-fits case returns the canonical tagged Nat with the complete store unchanged.
files: integration/talos/FirTalos/ConcreteResidentNatMul.lean; coordination/lanes/wasm-proof.md
contracts: none changed. The proof consumes the existing ImmediateNaturalPairRel, shared immediate-pair dispatcher/payload WP lemmas, stable makeNatural signature, scratch-slot cast, semantic Wasm ABI, concrete layout, and W7 mulFunction body. The constructor call is an explicit refinement boundary so a future general allocating makeNatural theorem closes the promoted corollary without changing this multiplication proof.
checks: Lean Beam update/sync/save for FirTalos/ConcreteResidentNatMul.lean passed with zero diagnostics and source hash 7a1606fc2b6d4eef; `lake -d integration/talos build FirTalos.ConcreteResidentNatMul` passed (3,079 jobs); `git diff --check main..0dcef319` passed; `make check` passed (704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713 unique cases, zero findings, 190 active bug cards, 25 mailbox tests); `make talos-setup` passed at Talos 0e05edbc; `make talos-check` passed (3,165 jobs). Final `git rebase main` was a no-op at f8c1069d.
bug-cards: none
blockers: none. The new standalone module is directly compiled and green; the integration owner must add its import to integration/talos/FirTalos.lean because W6 does not own the root umbrella.
handoff: Integration may validate and fast-forward functional commit 0dcef319 plus the containing tracked mailbox commit over f8c1069d, then add `import FirTalos.ConcreteResidentNatMul` to the integration-owned Talos umbrella and rerun make talos-check. No W7 implementation, fixture, profile, shared contract, root umbrella, or BOARD file was modified by W6.
next: Prove the general allocating makeNatural call theorem so the promoted tagged-pair product case becomes a closed corollary rather than an explicit constructor-boundary composition; otherwise consume the next active W6 operational request.
```
