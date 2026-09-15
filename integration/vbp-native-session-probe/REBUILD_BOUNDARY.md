# Imported specialization reset boundary

Request: `ROOT-W7-20260915-005`. Base:
`4ae817ab51e0f769c1766ddfbcb8143c7d31c0b2` (accepted partial-body repair plus
root's board update). Production compiler, source-view identities, toolchains,
runtime, W6 contracts and packages are unchanged in this investigation.

## Confirmed findings

The real renderer's final dependency rebuild selects 90 roots, including
`_private.Verso.Doc.0.Verso.Doc.ListItem.toJson` and generic
`_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map`, but not
`_private.Verso.Doc.0.Verso.Doc.DescItem.toJson`.

Imported compiler metadata shows that **both ListItem and DescItem use the
same specialization**, named under ListItem. Base-phase DescItem has two
calls to that helper. Its mono `_redArg` body also calls the helper's reduced
entry. Generated-name caller provenance therefore does not enumerate every
reader of a shared specialization.

`ResetSharing.lean` demonstrates the precise reset defect using the actual
imported metadata, without compiling or adding a source unit:

| Imported entry | Before root-local reset | After reset |
| --- | --- | --- |
| ListItem source owner | base body visible | imported base body hidden |
| Shared generated helper | base body visible; no kernel constant | base body and module mapping hidden |
| DescItem source reader | base body visible, calls helper twice | body and both calls still visible |

This is a violated compiler-context invariant, not a missing kernel definition
that should be copied into FIR. Upstream intentionally serializes compiler-only
generated declarations separately from kernel constants.

## Actual renderer failure boundary

`Boundary.lean` wraps the configured passes, forwarding each original call and
result without changing roots, order, bodies or checks. Bounded entry/exit
markers locate the failure in the real renderer run:

```text
base/specialize/0: 301 input declarations -> 392 output declarations
base/findJoinPoints/1: finished
base/simp/2: finished
base/cse/1: finished
base/saveBase/0: finished, 392 declarations
Unknown constant ...Array.mapMUnsafe.map._at_....ListItem.toJson.spec_0
```

There is no next pass-entry marker and no exception from a wrapped pass body.
Pinned upstream `LCNF.Main.runPassManagerPart` calls `checkpoint` immediately
after `pass.run`; `saveBase.shouldAlwaysRunCheck = true`. Thus the failure is
at the **mandatory post-saveBase checkpoint**, before mono lowering, final
impure capture, dependency-artifact assembly, or Wasm generation.

The earlier declaration-stat trace independently shows fresh ListItem
specialization `spec_120` generated in this rebuild. Regenerating that owner
does not rewrite old references retained in imported reader bodies. The exact
first fresh declaration rejected by the checkpoint has not been separately
reported; do not overstate the reader evidence as that declaration's identity.

Bounded actual-renderer log SHA-256:
`ba896afa90266c745875e37b94e7f7de6de81ed72c9cfd1cfd27c185c6a18566`.
Read-only before/after Beam snapshot SHA-256:
`33f0a93ee71421a2950791d4b95ac6eb884ac1852975b409b887538a1a2e4425`.
Local logs under `.deps/native-session-probe/control/` are disposable, not an
approval registry. A broad inherited compiler trace was stopped because of
excessive diagnostic memory; it is not successful gate evidence.

## Module-system interpretation and next decision

The problem supports a principled capture-context adaptation, but is not proof
that Lean 4.34 alone introduced the requirement. Both pinned 4.33 and 4.34
`LeanIR.lean` import target-private data with exported global visibility and
`loadIRSig := true`, then resume original postponed declaration groups. FIR's
private importer differs, but this renderer uses the **ordinary-source
fallback**, because the ordinary modules have no postponed groups.

Enabling postponement is not an established fix: the independent Html control
already fails in upstream leanir while ordinary module compilation succeeds.
Likewise, the reset's cross-reader defect is not repaired merely by changing
import flags in an unused provider.

Recommended next bounded experiment, requiring root's compilation-boundary
decision: capture final LCNF during the real owning module's ordinary frontend
compilation, preserving upstream declaration groups, private visibility and
specialization context. First test the implicated module boundary; do not
redesign every provider or change the LCNF backend. Imported prebuilt dependency
coverage remains a separate obligation even if this experiment succeeds.

The alternative is dependency-coherent invalidation/recompilation of imported
readers, not owner-name erasure alone. This would require a deliberate source-unit
policy rather than another named companion. Neither alternative is implemented
here. There is no sufficiently justified one-site behavior repair in this slice.

## Reproduce and checks

Use the unchanged source-view preparation, FIR-local 4.34 cache scope, and
worktree-local TMPDIR documented in `REPAIR_RESULT.md`:

```sh
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false build Probe
lake --keep-toolchain -KpostponeCompile=false env lean ResetSharing.lean
FIR_RENDERER_BOUNDARY=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Boundary.lean
```

- Both diagnostic files: Lean Beam, zero blocking diagnostics / saveReady.
- ResetSharing direct Lean: passes, confirms the existing defect (not a fix).
- Actual renderer Boundary run: expected exit 1 at the same helper, now localized.
- Focused Probe dependency build: passes, 677 jobs including reused jobs.
- `make check`: 730 cases / 2,172 comparisons, zero failures.
- Bug-card validation: 231 active cards; diff and mailbox checks pass.

See the lane handoff for final checkpoint checks. No fresh artifact, browser,
runtime performance or full renderer-closure acceptance is claimed. Bug card:
`FIR-BUG-wasm-none-reset-shared-specialization-reader`.
