---
id: FIR-BUG-wasm-none-final-capture-imported-specialization-reuse
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: Illuminate selection package regeneration
first-seen: 2026-08-14
reproduction: integration/illuminate-player/SelectionEmit.lean
regression: Fir/Wasm/Emit/SourceExamples.lean
---

# Summary

FIR's synthetic final-LCNF compilation can reuse an imported specialization
cache entry whose generated implementation belongs to an unrelated upstream
caller. Recursive source discovery then imports that caller's application
closure instead of generating the specialization in the selected source unit.

## Minimal reproduction

Compile Illuminate's selection player, whose comparison of two `Option Nat`
values specializes `Option.instBEq.beq`. The imported Lean environment already
maps the same specialization key to:

```text
Option.instBEq.beq._at_.Lean.PrettyPrinter.Delaborator.delabRange.spec_0
```

FIR follows the generated name's caller provenance and begins compiling the
pretty-printer closure. That unrelated closure eventually reaches
`Classical.ofNonempty`, and Lean rejects the synthetic unit as noncomputable.

## Exact commands

From `integration/illuminate-player`:

```sh
lake -KilluminateRoot=/tmp/fir-illuminate-source-6f build \
  IlluminateFirNative.SelectionCompile
lake -KilluminateRoot=/tmp/fir-illuminate-source-6f env lean SelectionEmit.lean
```

## Expected semantics

An isolated FIR source compilation cannot consume native object code behind an
imported specialization-cache name. Its fresh compiler unit must begin with an
empty specialization and closed-term cache, allowing Lean's ordinary passes to
generate helpers owned by the selected source caller. Cache state created
inside that compilation remains available to stop recursive specialization.

## Actual behavior

FIR removed only cache entries whose generated names were already owned by the
current source roots. A cache key for a generic callee can match while its
stored name belongs to an unrelated caller, so ownership filtering cannot make
imported specialization reuse sound for a self-contained artifact.

## Proof or differential evidence

The diagnostic closure trace maps the imported `Option.instBEq.beq`
specialization to `Lean.PrettyPrinter.Delaborator.delabRange`, then discovers
the Lean delaborator, elaborator, message, and syntax closures before failing.
None is reachable from the real animation state machine.

## Semantic impact

Valid isolated functions can fail capture, acquire large unrelated closures,
or retain generated imports whose implementation exists only in a native Lean
module. The selected source closure and its measured compilation cost are both
incorrect.

## Classification and triage

This is a generic final-LCNF compiler-unit isolation bug, not an Illuminate
façade or resident-runtime omission.

## Workaround

None. Retaining application-specific generated names would make the native
object dependency implicit and non-portable.

## Upstream tracking

none

## Resolution and regression

Synthetic source compilation now preserves imported generated-name mappings
for direct dependencies but starts each compiler unit with empty
specialization and closed-term caches. It still removes mappings owned by the
roots being regenerated. The compiler repopulates both caches normally within
the unit.

`optionNatChangedFixture` exercises the colliding `Option Nat` specialization
in the same Lean environment and rejects any leaked pretty-printer source.
Source-root discovery also rejects declarations marked noncomputable before
promoting them into a later frontier, matching Lean's code-generator boundary.
The unchanged Illuminate selection entries then regenerate without the
unrelated meta closure.
