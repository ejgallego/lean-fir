# wasm-gen lane

Current slice: `ROOT-W7-20260915-005`, renderer rebuild-boundary investigation.
Root owns integration and compilation-boundary decisions. Packages are untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 4ae817ab51e0f769c1766ddfbcb8143c7d31c0b2
functional-head: cd130bcaf10c7b76d332b44031fe54ffe8b9b627
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Confirm imported shared-specialization reset defect and locate actual renderer rejection at mandatory post-saveBase checkpoint. Evidence only; no production repair or unit-policy change.
files: integration/vbp-native-session-probe/{Boundary.lean,ResetSharing.lean,REBUILD_BOUNDARY.md,README.md}; bugs/FIR-BUG-wasm-none-reset-shared-specialization-reader.md; coordination/lanes/wasm-gen.md
contracts: none changed; compiler, toolchains, runtime, W6 and package contracts untouched
checks: Diagnostic Beam zero blocking errors/saveReady; ResetSharing direct 4.34 Lean passes and confirms defect. Actual Boundary renderer capture exits 1 at same helper after base/saveBase/0, before mono; no complete capture claimed. Probe dependency build passes 677 jobs. make check passes 730 cases/2172 comparisons. make talos-check passes after existing setup, 3205-job cone plus 3166-job trust stage. Gate commands ran the final functional file content while the functional commit was being recorded, not a new exact-HEAD artifact attestation. Bug-card validator passes 231 cards; diff/mailbox checks pass. No artifact emission or browser gate in this diagnostic-only slice.
bug-cards: FIR-BUG-wasm-none-reset-shared-specialization-reader
blockers: Root-local mapping invalidation leaves DescItem imported base/mono reader of ListItem-owned shared specialization visible. Real renderer rejects during mandatory base validation; full closure still unavailable.
handoff: Clean local-only investigation checkpoint for root review. Canonical completion pins containing status commit. No main/push/publication/pointer change.
next: Root decides bounded owning-module ordinary frontend capture experiment versus dependency-coherent imported-reader invalidation. No manual companion, named seed, precompiled closure injection, disabled check or blanket module regrouping. Stop at this decision boundary. ABI/projection/join work remains separate.
```

## Finding

Lean's original Verso.Doc compilation shares a ListItem-named specialization
with DescItem. Removing that helper's imported mapping does not remove the
DescItem reader. The helper has no kernel constant, so the retained calls become
unresolvable. Read-only Beam and direct batch diagnosis confirm this transition.

Actual renderer: 90 requested rebuild roots include ListItem but not DescItem.
Fresh specialization occurs; the final base unit has 392 declarations.
Bounded markers show saveBase completes, followed by the same unknown-helper
exception from its mandatory checkpoint; mono/final-impure/artifact assembly
are not reached. The exact first fresh declaration rejected remains unreported.

Log SHA-256:
`ba896afa90266c745875e37b94e7f7de6de81ed72c9cfd1cfd27c185c6a18566`.
See `integration/vbp-native-session-probe/REBUILD_BOUNDARY.md` for reproduction,
upstream comparison, limitations and the recommended next experiment.

This is not established as a 4.34-only regression: relevant upstream module
import setup also exists in 4.33. The ordinary/postponed control remains separate;
simply enabling postponement is not a validated fix. Production stays on 4.33,
the isolated consumer/source-view probe on exact 4.34.0-rc2. No performance claim.
