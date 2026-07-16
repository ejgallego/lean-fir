---
id: FIR-BUG-wasm-none-compiler-nat-literal-kind
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-17
reproduction: Fir/Wasm/Emit/SourceExamples.lean
regression: Fir/Wasm/Emit/SourceExamples.lean
---

# Summary

The Wasm supported-domain validator rejects Lean 4.32's compiler-produced small `Nat` literal because the local is typed `tagged` while `acceptsLiteralInvariant` classifies every `.nat` literal as `tobject`.

## Minimal reproduction

Compile `Fir.Validation.Corpus.Source.litNat`, whose source is `def litNat : Nat := 42`, with `Fir.Validation.Lcnf.compileEntry`. Lean emits a final-impure declaration returning `tobj` whose literal binding has type `tagged` and value `.lit (.nat 42)`.

## Exact commands

Run `lake build Fir.Wasm.Emit.SourceExamples` from the repository root. The first command elaboration guard captures the real compiler output and checks that `compileClosed` reaches the specific `unsupportedCode` rejection recorded here.

## Expected semantics

The compiler-produced final-impure declaration should inhabit the Wasm supported domain. A small `Nat` literal has a tagged runtime representation, and the lowerer's `AbiKind.acceptsLiteral` already accepts `.nat` for `tagged`, `object`, and `tobject` result kinds.

## Actual behavior

`supportedLetDeclKind?` calls `AbiKind.acceptsLiteralInvariant`. That function assigns `.nat` the kind `tobject` and asks whether it refines the declared `tagged` kind. It does not, so `lowerSupported` returns `validation (unsupportedCode Fir.Validation.Corpus.Source.litNat)` before the lowerer can handle the otherwise-supported literal.

## Proof or differential evidence

The compiler capture reports declaration result type `tobj`, literal-binding type `tagged`, and `abiValueKind?` equal to `some tagged`; `supportedDecl` nevertheless evaluates to `false`. Replacing the source with the analogous `UInt64` literal produces an 88-byte validated Wasm module through the same bridge.

## Semantic impact

The most basic closed `Nat` source declaration cannot use the source-to-Wasm bridge. More generally, the declared invariant does not describe the representation refinement Lean 4.32 actually records for statically small natural literals.

## Classification and triage

This is a Wasm-adapter domain mismatch, not evidence that Lean evaluates the literal incorrectly. It complements `FIR-BUG-wasm-none-object-nat-fixture`: that card records a hand-built heap-only annotation, while this card records the real compiler's more precise `tagged` annotation. Changing the shared invariant belongs in the W4 contract/proof lane.

## Workaround

The source-emission smoke test uses the compiler-produced closed `UInt64` literal. The bridge does not normalize the captured `Nat` program or weaken the frozen supported-domain check.

## Upstream tracking

none

## Resolution and regression

unresolved
