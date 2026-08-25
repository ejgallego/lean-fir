---
id: FIR-BUG-wasm-none-generic-inhabited-fallback-trap
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: runtime-audit
first-seen: 2026-08-25
reproduction: Fir/Wasm/Emit/ResidentFallback.lean
regression: integration/talos/artifact/FirWasmSourceExample.lean
---

# Summary

The generic closed-application resident policy replaces
`instInhabitedOfMonad._redArg` with an unconditional Wasm trap. Lean 4.33
defines the corresponding `Inhabited (m α)` default as `pure default`, so a
source closure that reaches this declaration succeeds natively but traps after
resident linking.

## Minimal reproduction

`ResidentFallback.inhabitedFunction` has the source signature
`(object, tobject) -> tobject` and body `[.unreachable]`. The standalone
resident fallback artifact exports this helper, and its JavaScript client
currently asserts that calling it traps.

The exact Lean 4.33 source definition is:

```lean
instance {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] :
    Inhabited (m α) where
  default := pure default
```

## Exact commands

```sh
lake exe fir-wasm-artifact resident-fallbacks \
  integration/talos/artifact/_build/resident-fallbacks.wasm
node integration/talos/artifact/run-resident-fallbacks.mjs \
  integration/talos/artifact/_build/resident-fallbacks.wasm
sed -n '3896,3903p' \
  ~/.elan/toolchains/leanprover--lean4---v4.33.0/src/lean/Init/Prelude.lean
```

## Expected semantics

If the captured declaration is reachable, the linked helper must apply the
captured monad's `pure` operation to the represented default value and return
the result with the same ownership behavior as native Lean. Alternatively,
generic resident linking must reject the closure until that implementation is
available.

`panicCore` is a distinct failure operation and may retain its own fail-closed
policy. It does not justify changing the semantics of the inhabited instance.

## Actual behavior

`ResidentLinker.closedApplicationFamilySteps` includes
`.fallbacksAvailable`. Whenever the captured module imports
`instInhabitedOfMonad._redArg`, `ResidentFallback.internalizeAvailable`
removes that import and installs `inhabitedFunction`, whose only instruction is
`unreachable`. The linker's zero-import and no-runtime-operation
postconditions then pass.

## Proof or differential evidence

The resident fallback client directly establishes the target trap. The Lean
Prelude establishes the successful source result. No linker premise proves
that the declaration is unreachable, and the generic closed-application policy
is used by closures beyond the reviewed prettyM entry.

## Semantic impact

A pure source module can satisfy the complete zero-import package contract and
still disagree with native Lean on a valid reachable path. The present prettyM
corpus is unaffected because its retained weak-inhabited fallback is asserted
unreached, but corpus reachability is not a generic runtime contract.

## Classification and triage

This is a resident-link implementation gap at the external-to-resident
boundary. Import closure is correct as a syntactic statement; semantic closure
is not.

## Workaround

The accepted prettyM packages rely on their reviewed entry-specific
unreachability tests. Do not extend that assumption to a new closed
application merely because the same external declaration appears in its
capture.

## Upstream tracking

none

## Resolution and regression

The generic source-internalization path now discovers and compiles the real
`instInhabitedOfMonad._redArg` final-LCNF body. Closure admission queries the
same fixed-capture candidates as executable lowering, so the dictionary's
valid underapplication is admitted rather than forcing an external boundary.

`ResidentFallback` retains only `panicCore`; its standalone zero-import client
asserts exactly that fail-closed policy. The reachable
`inhabitedMonadDefaultProbe` keeps generic dictionary construction across a
`@[nospecialize]` boundary and returns `42` in native Lean, FIR's LCNF
interpreter, and the zero-import Wasm artifact. The concrete source-product
gate executes and deterministically byte-compares that artifact with the rest
of the compiler-produced corpus.

The probe deliberately uses `UInt32` state. The separately recorded
`FIR-BUG-impure-none-uint64-box-tagged` concerns FIR's incorrect small
`UInt64` boxing representation and is not a reason to restore this trap.
