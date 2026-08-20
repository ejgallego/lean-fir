---
id: FIR-BUG-wasm-none-individual-hit-scene-generated-helper-admission
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-20
reproduction: integration/illuminate-hit-scene/ProbeIndividual.lean
regression: integration/illuminate-hit-scene/ProbeIndividual.lean
---

# Summary

FIR's former per-source-root capture could regenerate a private closed name
with a scalar body while a regenerated caller retains the imported boxed ABI
for that same name. Wasm admission rejects the resulting inconsistent closure;
the first reported declaration is Lean's generic
`_private.Init.Data.Array.Basic.0.Array.forIn'Unsafe.loop._redArg` helper.

## Minimal reproduction

Use clean Illuminate revision
`88dcfee895a55e804641bff485024cffec1b5419`, build its real HitScene modules
under FIR's Lean 4.33 toolchain, and capture `Illuminate.HitScene.query` with
`compileEntryIndividuallyInternalized`.

## Exact commands

```sh
cd integration/illuminate-hit-scene
TMPDIR=$PWD/../../.deps/tmp \
ILLUMINATE_ROOT=$PWD/../../.deps/source-views/illuminate-hit-scene \
  lake --keep-toolchain --reconfigure \
    -KilluminateRoot=$PWD/../../.deps/source-views/illuminate-hit-scene \
    build IlluminateFirHitScene.Compile
TMPDIR=$PWD/../../.deps/tmp lake --keep-toolchain env lean \
  -DmaxHeartbeats=0 ProbeIndividual.lean
```

## Expected semantics

The captured declarations are ordinary final LCNF emitted by Lean for the
real query closure. FIR should either admit and lower their exact ABI/ownership
forms or identify a real unsupported semantic operation. Generated-name
spelling must not select a declaration-specific substitute.

## Actual behavior

Capture completes with 426 declarations and 55 external declarations. Eleven
declarations fail `supportedDecl`; `validateSupported` stops at the generic
Array loop. Bypassing admission for diagnosis makes the lowerer report that a
call to `Illuminate.Vec2.east._closed_1` has an incompatible let ABI. The
captured program declares that name as `Float`, while
`Illuminate.Vec2.east._closed_2` calls it as a boxed object and unboxes the
result. The full list and formatted bodies are written to
`_build/hit-scene-probe.json` and `_build/hit-scene-unsupported.lcnf`.

## Proof or differential evidence

The failure occurs before resident linking and external-engine execution. The
same source modules compile through Lean's ordinary native pipeline. The prior
postponed whole-module capture hid this generic closure behind a narrower
specialized module frontier and therefore does not establish that the generic
form is unsupported.

## Semantic impact

This blocked migration of the HitScene package to the generic native-like
source capture path and prevents a faithful inventory of its source-compiled
Float and residual libm boundary.

## Classification and triage

Compiler source-capture debt. Admission is correctly refusing the inconsistent
object/scalar closure and must not be weakened. The repair must preserve Lean's
source-unit ownership and generated-name identities; it must not special-case
Illuminate or this private declaration name.

## Workaround

Production HitScene capture previously replayed the exact postponed entry module through
`compileEntryModuleWiseInternalizedFrom`, then closes ordinary imported source
with `internalizeFinalDependencies`. This is the generic module-preserving
composition used by the Verso packages. It did not weaken admission or add a
declaration-specific runtime helper, but it grouped ordinary imported roots
into one synthetic dependency unit.

## Upstream tracking

None.

## Resolution and regression

`compileEntryIndividuallyInternalized` now distinguishes two upstream source
boundaries. A public entry in a postponed module is resolved through Lean's
module `constNames` index and replayed as its exact deferred declaration
groups, even though it has no imported impure signature. Ordinary imported
roots are captured independently at the final-impure pass after their owned
compiler mappings are reset. The final merged graph is pruned from the public
entry, removing generated boxed adapters that were emitted alongside a root
but are not reachable.

No admission rule was weakened and no Illuminate declaration is named by the
generic repair. `ProbeIndividual.lean` now requires zero unsupported
declarations, successful `validateSupported`, and successful Wasm lowering. It
records 313 reachable declarations, 53 externals, and 261 base functions. The
published candidate retains the exact five-function libm frontier, has zero
final imports, passes all 301 fixture queries and the 10,000-query flat-arena
test, and shrinks the complete Wasm module from 67,556 to 64,217 bytes.
