---
id: FIR-BUG-wasm-none-lcnf-capture-environment-pollution
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-20
reproduction: Fir/Wasm/Emit/SourceExamples.lean
regression: Fir/Wasm/Emit/SourceExamples.lean
---

# Summary

Repeated final-LCNF capture with overlapping dependency roots leaves Lean's
compiler phase extensions in the elaborating module environment. Subsequent C
emission sees an inconsistent final declaration order and prints internal
compiler panic backtraces despite completing the Lake target successfully.

## Minimal reproduction

Recursively call `Fir.Validation.Lcnf.compileEntry` for one entry while adding
new helper roots after each capture. Then allow Lean to native-compile the
module containing that command.

## Exact commands

```sh
lake --no-cache --rehash build Fir.Wasm.Emit.SourceExamples
```

## Expected semantics

Artifact-only compiler probing should return the captured declarations without
changing the module environment that Lean later uses for its ordinary native
code emission.

## Actual behavior

`LCNF.main` records final declarations in environment extensions. Repeated
overlapping runs accumulate phase state, and `LCNF.getImpureDeclIndices`
eventually reports `i != 0` and `map.size == targets.size` assertion failures;
the following declaration sort also reports missing hash-map keys.

## Proof or differential evidence

The `Std.Format.prettyM` recursive-internalization build emitted millions of
bytes of repeated `getImpureDeclIndices` and `DHashMap.get!` panic backtraces.
The OLean target and generated Wasm still completed, confirming that the noise
comes from polluted later C emission rather than the returned artifact.

## Semantic impact

Generated Wasm is unaffected in the observed run, but a successful build is
not operationally clean and future compiler changes could turn the latent
environment inconsistency into a hard failure.

## Classification and triage

This is a Wasm-adapter lifecycle issue: the capture API invokes a stateful
compiler entry point for inspection and must restore the caller's environment
after collecting the artifact.

## Workaround

Wasm source capture runs `LCNF.main` under `Lean.withoutModifyingEnv`. The
artifact is collected inside that scope and remains usable after the caller's
environment is restored.

## Upstream tracking

none

## Resolution and regression

Resolved in the Wasm generation lane. `Fir/Wasm/Emit/SourceExamples.lean`
asserts that recursive Format capture leaves the local impure-declaration
inventory unchanged. A forced build completes without compiler panic output.
