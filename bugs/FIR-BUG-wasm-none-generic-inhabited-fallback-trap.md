---
id: FIR-BUG-wasm-none-generic-inhabited-fallback-trap
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: runtime-audit
first-seen: 2026-08-25
reproduction: Fir/Wasm/Emit/ResidentFallback.lean
regression: integration/talos/artifact/resident-fallback-client.mjs
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

Unresolved. Prefer compiling or reusing the real Lean definition. If that is
not yet supported, split the semantically valid `panicCore` behavior from the
inhabited instance and make the generic linker reject the latter. Add a native
versus emitted-Wasm reachable-entry differential before marking the repair
generation-ready.
