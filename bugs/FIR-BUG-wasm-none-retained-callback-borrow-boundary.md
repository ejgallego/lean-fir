---
id: FIR-BUG-wasm-none-retained-callback-borrow-boundary
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-02
reproduction: integration/vbp-verso-viewer/check.sh
regression: integration/vbp-verso-viewer/package-smoke.mjs
---

# Summary

The VBP browser adapter re-enters a retained Lean callback through an owned
bridge parameter, so the first invocation consumes the closure and a later
React render traps on the released address.

## Minimal reproduction

Compile the real VBP widget at commit
`cad90a2f59544833a81a456b72a0fd52d8f28b1c` with VIR commit
`90aa3f4938152d455ce4d5ddb79073729fc2df71`. Mount one representative
`Preview.ready` document, retain the component callback handed to
`react.root.renderComponentIntoSelector`, and invoke that same callback twice
through `FirVbpVersoViewer.Bridge.invokeComponent`.

The first invocation returns a React node. The second invocation reaches
`unreachable`; the callback address no longer denotes a live resident
allocation.

## Exact commands

The permanent package regression will be:

```sh
cd integration/vbp-verso-viewer
bash check.sh
```

The failure was also reproduced with accepted package
`1fb8b65a2730-cad90a2f5954-90aa3f493815-ebe016531bae395081c3`, whose Wasm
SHA-256 is
`d738584215ea9c4b3eabef3aa290245c49fc54e2128d0dddf303db82cdc26a66`.

## Expected semantics

VIR's generic React host owns a retained callback lease and may invoke the
same component, event, state, or effect callback more than once before it
releases that lease. Re-entering Lean must borrow the retained closure for
each invocation. Lean's explicit reference-counting pass should establish the
corresponding physical ABI.

## Actual behavior

All five neutral bridge declarations accept their callback as an ordinary
owned parameter. Their final-LCNF public signatures therefore expose
`object`, and invoking a bridge consumes the host-retained address. The
JavaScript lease remains logically live while its Wasm closure has been
released.

The accepted smoke passed because its fake host invoked each newly generated
callback only once. The full provider-neutral FLT Chromium campaign permits a
repeat render and traps in `FirVbpRuntime.callCallback`.

## Proof or differential evidence

The same original payload and ten alternating updates pass through interpreted
VIR. FIR alone also renders the exact ready payload when every generated
callback is invoked once. A two-call callback probe deterministically fails on
the second call, isolating the discrepancy from RpcJson encoding, closure
dispatch admission, and the real React host import frontier.

## Semantic impact

Any browser package that transfers a Lean closure to a retained host API can
trap on a legitimate repeat callback. Components are the first observed case;
event handlers, state updaters, and effect setup/cleanup actions share the same
bridge design.

## Classification and triage

This is a generic adapter/application-boundary ownership defect. It is not a
VBP semantic error and does not require a widget-specific host shim. The
accepted HitScene retained-root boundary already demonstrates the appropriate
source-level borrowed façade pattern.

## Workaround

None. Do not mark arbitrary closure graphs persistent from JavaScript and do
not add named callback shims to resident runtime generation.

## Upstream tracking

none

## Resolution and regression

All five neutral callback bridges now annotate the retained closure parameter
with Lean's `@&` borrowed convention. Lean 4.34 final LCNF consequently emits
`inc[ref] callback` immediately before each consuming closure application,
leaving the host-owned root live for later invocations without a named runtime
shim or persistent graph marking.

The package smoke encodes a representative `Preview.ready` document and calls
the same retained root component twice before unmounting. The regenerated
module passes with 2,399 captured declarations, 2,247 source functions, 5,360
resident helpers, 41 reviewed host imports, and no FIR runtime operations. The
remaining full-FLT failure is separately tracked as
`FIR-BUG-wasm-none-resident-arena-released-block-reuse`.
