---
id: FIR-BUG-wasm-none-duplicate-declaration-parameters
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-08
reproduction: Fir/Wasm/Examples.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

`WasmSupported` admits duplicate declaration parameter identifiers even
though lowering collapses them to one symbolic Wasm parameter, producing an
invalid call signature.

## Minimal reproduction

Define an internal declaration with two `tobject` parameters carrying the
same `FVarId`, return that identifier, and call the declaration with two
object arguments. Source `bindParams` accepts both arguments and its lookup
observes the later binding.

## Exact commands

Run:

```text
lake build Fir.Wasm.Examples
```

The permanent regression records that the duplicate-parameter program is not
supported and that `lowerSupported` rejects it before symbolic module
validation.

## Expected semantics

Every program accepted by `WasmSupported` must lower to a module whose
declaration parameter row agrees with the parameter kinds used to validate
direct calls. Malformed same-scope duplicate binders should be rejected at the
support boundary.

## Actual behavior

At discovery, `supportedProgram` returned `true` and
`declarationParameterKinds?` returned two `tobject` lanes. In contrast,
`addDeclarationParams` uses `insertLocal`, which retained only one physical
parameter. The caller emitted two operands and `validateModule` rejected the
lowered module with a stack mismatch: one declared result versus two values
remaining after the one-parameter call.

## Proof or differential evidence

The W6 callee-entry proof needs the validator's parameter-kind row to align
with the generated function's exact parameter-local row. The reproduction
gives rows of lengths two and one respectively, so that invariant and the
resulting compiler-correctness theorem are false on the admitted domain.

## Semantic impact

An accepted program can produce an invalid symbolic Wasm module. More
specifically, recursive direct-call correctness cannot construct a callee
entry frame from every validator-approved argument vector.

## Classification and triage

This is a compiler support-domain bug. LCNF `FVarId`s are same-scope binder
identities; silently alpha-renaming an ambiguous duplicate parameter would
invent a source distinction that lookup does not expose. The clean boundary
is to reject duplicate declaration parameter identifiers before lowering.

## Workaround

Duplicate declaration parameters are rejected at the Wasm support boundary.
Upstream producers should maintain unique same-scope `FVarId`s.

## Upstream tracking

none

## Resolution and regression

Resolved by adding `declarationParameterIdsUnique` to `supportedDecl`.
`Fir/Wasm/Examples.lean` preserves the original raw-lowering failure as an
oracle, checks rejection by both `supportedProgram` and `lowerSupported`, and
retains the adjacent valid direct-call program as a positive regression.
