---
id: FIR-BUG-wasm-none-isolated-export-ownership
status: candidate
classification: lcnf-capture
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: lcnf
pass: inferBorrow
discovered-by: differential-test
first-seen: 2026-09-02
reproduction: Fir/Wasm/Emit/SourceExamples.lean
regression: none
---

# Summary

FIR's isolated imported-entry capture hides the source root's module mapping
before recompilation but does not preserve its `@[export]` annotation. Lean's
ordinary `InferBorrow` pass consequently treats an exported reference
parameter as borrowed instead of owned.

## Minimal reproduction

Compile an imported definition of the following shape through
`compileEntryIndividuallyInternalized`:

```lean
@[export fir_source_owned_entry_fixture]
def ownedEntry (_value : Array Nat) : Unit := ()
```

The ordinary Lean C pipeline emits a `lean_dec_ref` for `_value`. Before this
repair, FIR's captured final LCNF instead contains an `@&_value` parameter and
no decrement.

## Expected semantics

FIR should follow Lean's ordinary exported-entry ABI. `InferBorrow` initializes
unannotated possible-reference parameters of an exported declaration as owned,
while a source-level explicit `@&` annotation remains borrowed.

## Actual behavior

`forgetGeneratedCompilerModuleMappings` removes the imported source root from
`const2ModIdx` to prevent stale imported LCNF bodies from satisfying the fresh
synthetic compilation. Parametric attributes use that same mapping to locate
their imported module entries. The later `Lean.isExport` query therefore
returns false even though the original environment contains the export name.

## Proof or differential evidence

In the VBP retained-component bridge, ordinary Lean 4.34 emits
`lean_dec_ref(callback)` for all five typed release facades. The exact FIR
capture records all five parameters as borrowed, produces byte-identical Wasm
after adding the facades, and leaves the retained callback census unchanged.

## Semantic impact

An application can transfer an owned reference to a compiled exported entry
and reasonably expect the entry to consume it. FIR instead retains the object,
causing reference-count and resident-heap leaks. The mismatch is generic and
is not specific to callbacks or VBP.

## Classification and triage

Preserve each imported root's export annotation in the synthetic local
environment before running Lean's normal compiler pipeline. Do not patch
borrow bits or insert decrements after final LCNF; those approaches would skip
upstream ownership inference and explicit-RC placement.

## Workaround

none

## Upstream tracking

none; this is caused by FIR's synthetic source-unit cache reset.

## Resolution and regression

unresolved
