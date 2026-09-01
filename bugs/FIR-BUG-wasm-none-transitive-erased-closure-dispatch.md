---
id: FIR-BUG-wasm-none-transitive-erased-closure-dispatch
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-01
reproduction: integration/vbp-verso-viewer/check.sh
regression: integration/vbp-verso-viewer/check.sh
---

# Summary

FIR omits a compiler-generated boxed closure target from a generic closure-call
dispatch chain when its hidden world parameter reaches an erased parameter
through another structurally erased forwarding declaration.

## Minimal reproduction

At VBP commit `cad90a2f59544833a81a456b72a0fd52d8f28b1c` with VIR
commit `90aa3f4938152d455ce4d5ddb79073729fc2df71`, compile and link the
real entries

- `VersoBlueprint.Experimental.VirPreview.Widget.mount`;
- `VersoBlueprint.Experimental.VirPreview.Widget.unmount`;

together with a neutral exported bridge that invokes a retained
`Unit → ReactM (Js Node)` callback.

`mount` transfers the compiler-generated closure
`Lean.Vir.React.Root.renderComponentIntoSelector._redArg._lam_0._boxed` to
the reviewed React host binding. Calling that closure synchronously through
the bridge traps.

## Exact commands

The permanent exact-source, immutable-package regression is:

```sh
cd integration/vbp-verso-viewer
bash check.sh
```

The source cone captures 2,399 declarations. After closing 111 of the 152
reviewed capture externals, the generated 6,278,717-byte module has zero FIR
runtime operations and exactly the 41 reviewed VIR React/browser imports.
Package construction reaches `node smoke.mjs` before trapping in the callback.

## Expected semantics

The boxed wrapper is a valid closure target with total arity four and two
captures. Its remaining `Unit` and hidden world arguments are compatible with
the bridge call. The hidden world argument is semantically erased: the wrapper
forwards it to the unboxed declaration, whose corresponding parameter is
itself structurally erased.

FIR should include the boxed target in the generated dispatch and the retained
component callback should execute synchronously, matching Lean's ordinary
explicit-boxing and IO calling convention.

## Actual behavior

The live closure header is valid and resolves to dispatch row 161, target
`Lean.Vir.React.Root.renderComponentIntoSelector._redArg._lam_0._boxed`,
arity four, fixed count two, and capture descriptor `[object, tobject]`.

The symbolic body for `FirVbpVersoViewer.Bridge.invokeComponent` contains a
candidate for the unboxed `_lam_0` declaration but no candidate for its actual
`_boxed` target. The chain reaches its terminal `unreachable`, producing a
Wasm trap before the component body invokes any further host operation.

## Proof or differential evidence

The same exact widget and synchronous callback lifecycle pass through VIR at
the accepted FLT checkpoint `410d9087d3b05e32864eb0d6f53c3404e51f6d52`.
FIR's `unmount` path already passes through the same adapter and physical
`EStateM.Result` boundary, isolating the discrepancy to closure dispatch.

## Semantic impact

Any FIR package that re-enters a compiler-generated boxed IO/React callback
through a separately compiled generic bridge can trap even though the closure
metadata and ordinary Lean call are valid. This blocks reusable native browser
providers with retained components, effects, state updaters, or event
handlers.

## Classification and triage

`erasedOnlyParameter` currently recognizes only forwarding to a parameter
whose raw final-LCNF type is erased. The generated boxed wrapper forwards its
world parameter to a `tobject` parameter whose declaration body proves the
same erased-only property. The erased-lane analysis therefore needs bounded
transitive propagation through named forwarding declarations; matching
`_boxed` names or admitting erased-to-object compatibility globally would be
unsound workarounds.

The implementation is a shared `Fir/Wasm/Lower.lean` contract and must be
coordinated with W6's declaration-aware ABI proofs.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The shared lowering classifier now follows only compiler-generated `tobject`
and explicit-boxing `tagged` carriers through statically named declaration
parameters to raw `erased` or `void` sinks. The query is bounded and
cycle-safe; unknown declarations, external carrier parameters, arity
mismatches, cycles, and exhausted fuel fail closed. No global
object/erased or tagged/erased compatibility was added.

W6's declaration-aware cache, structured-validation, and final-LCNF typing
proofs consume the same effective classifier. The production-shaped
`tobject -> tagged -> void` regression passes, and the exact VBP package
regenerates deterministically with 2,399 captured declarations, 2,247 source
functions, 5,360 resident helpers, 41 host imports, and 6,239,344 Wasm bytes
at SHA-256
`d738584215ea9c4b3eabef3aa290245c49fc54e2128d0dddf303db82cdc26a66`.
Its synchronous mount, callback/event, effect, update, and unmount lifecycle
passes.
