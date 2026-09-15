# wasm-gen lane

Continuous renderer investigation: `ROOT-W7-20260915-031`. Root accepted the
provider-link checkpoint in `-035`; this successor supplies the two authorized
existing-contract primitives. Routing update `-036` is acknowledged: subsequent
VBP runs start from official `tooling/lean-4.34` or a W7-owned child, not another
FIR source overlay. Root retains integration ownership; W6 remains untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 4c0c8917a09f097dbe692fca50230dbe61a814cc
functional-head: 422caea960af963026522b58e85c6e95f941dc32
contract-base: ac9f728a609e82a9476027c0459dc73855c4e78a
clean-at-update: true
slice: Arbitrary-limb natural literal allocation and ABI-exact UInt64.ofNatLT coverage.
files: ResidentLiteral.lean; ResidentFixedWidth.lean; artifact primitive/metadata tests and gate; renderer diagnostic preparation/ratchet/README; bug card; lane status
contracts: none; no W6, shared ABI/layout/effect, consumer source, host policy, toolchain pin or package-pointer changes
checks: Beam implementation modules and installed-metadata test: zero errors. Focused production cone 20 jobs and direct metadata test pass, repeated after rebase. Installed 4.34 metadata test passes. make check: 730 cases/2172 comparisons, 235 bug cards. make talos-check: 3205 jobs and forced 3166-job trust audit. Artifact check.sh: pass. Standalone literals/fixed-width tests pass raw and Binaryen-optimized. Diff check passes. Rebase only adds AGENTS/board routing policy; implementation trees unchanged.
bug-cards: FIR-BUG-wasm-none-arbitrary-natural-literal (fixed)
boundary: single fresh renderer lowering reduces 17 imports to 15, with zero runtime operations; strict admission rejects String.Internal.atEnd. No full renderer execution or new two-run renderer acceptance claimed.
handoff: Clean production primitive checkpoint for root review. Investigation remains in-progress; no W7 main landing, push or publication.
next: Route the renderer fixture through official tooling/lean-4.34 at 348f42f832983949dd1514ed700820cf9c6c05c3, then address the three String declarations within root-authorized scope. JS stays audit-only pending an explicit host-boundary report.
```

## Representation and evidence

Large natural literals use canonical `naturalLimbs`, checked limb count/extent,
the big-natural marker, live/nonpersistent flags and reference count one.
Immediate/promoted representations are unchanged; overlarge tagged results
remain rejected. Tests cover the first one-limb big Nat, `2^64`, a four-limb
mixed value, all payload/header words over poisoned memory, scratch restoration
and independent ConcreteHost decoding.

`UInt64.ofNatLT` retains its erased proof parameter and otherwise reuses the
existing `UInt64.ofNat` body. Tests check the actual installed extern symbol,
safe/pure UInt64 result, parameter types and borrowing under 4.33 and 4.34,
plus execution through the full valid range including `2^64 - 1`.

The source closure remains 52 modules / 1535 bodies / 16 provider links.
Base Wasm remains 839735 bytes, SHA-256
`b154b7169d63c3aa02098b0f5936f0dee4d2fa5cc40a234ffcfaa8d602a0af9b`.
The remaining native declarations are `String.Internal.atEnd`,
`String.Internal.get`, and `String.Pos.Raw.atEnd`, alongside the unchanged 12
VIR imports. No export provider remains unresolved.

The completed single lowering is at `.deps/native-session-probe/runtime-frontier-lowering/`.
It used the accepted compacted artifact whose SHA-256 remains
`7d3124e258fe8e17964bb9a6d6c7b609bffddcf1669b12fdced077b0cb40d482`
(preserved under `native-provider-product/repeat/`). The later fresh two-run
capture was stopped after the official-lane directive; its `first/` is incomplete
and is not evidence. No new work claims the official 4.34 baseline yet.

Logs: `.deps/native-session-probe/control/runtime-frontier-*`. The first check
attempt exposed bug-card formatting, then overlapping artifact/check scratch
caused an operational file race. Formatting is fixed and the final gates ran
successfully with artifact/check serialized. No semantic failure was hidden.
Existing refinement theorems are not extended by this generation checkpoint.
