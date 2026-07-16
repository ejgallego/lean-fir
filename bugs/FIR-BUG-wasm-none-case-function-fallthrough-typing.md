---
id: FIR-BUG-wasm-none-case-function-fallthrough-typing
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential
first-seen: 2026-07-16
reproduction: Fir/Wasm/Lower.lean#compileCaseChainWith
regression: integration/talos/artifact/check.sh
---

# Summary

Constructor-case lowering emits zero-result `if` instructions at the tail of
a result-producing function. FIR's symbolic checker and Talos's partial
validator accept the branches because they all return or trap, but a standard
WebAssembly validator treats the zero-result `if` as an empty fallthrough and
rejects the function end.

## Minimal reproduction

Lower and encode either `abiCaseProgram` or `abiDefaultCaseProgram`. Both
functions return one `i32` handle and end in a nested constructor-case `if`.
The emitted `if` has empty block type `0x40`; Node reports that the function
falls through with zero values where one result is required.

## Exact commands

From the artifact worktree:

```sh
lake -d integration/talos/artifact exe fir-wasm-artifact all /tmp/fir-wasm-artifacts
node -e 'const fs=require("fs"); for (const name of ["case.wasm","default-case.wasm"]) WebAssembly.compile(fs.readFileSync("/tmp/fir-wasm-artifacts/"+name)).catch(error => console.log(name,error.message))'
```

## Expected semantics

Every validated function whose symbolic control-flow result has no
fallthrough should encode as a standards-valid Wasm body with no observable
fallthrough path.

## Actual behavior

`Instruction.ifElse` carries no result or reachability annotation, and the
Talos adapter maps it to `.iff 0 0`. At a function returning one value, the
standard validator therefore observes a reachable zero-value function end.

## Proof or differential evidence

Node 24 validates the emitted literal and constructor/projection modules but
rejects both case modules with `expected 1 elements on the stack for fallthru,
found 0`. The same symbolic modules pass FIR and Talos validation.

## Semantic impact

The initial case corpus cannot be emitted as portable Wasm by a direct
instruction-for-instruction serialization, despite executing in Talos. This
also shows that Talos validation is not sufficient evidence of standard Wasm
validation for terminal structured control flow.

## Classification and triage

This is a Wasm-adapter/control-typing gap. Source case evaluation and the
symbolic no-fallthrough analysis agree; the missing information is at the
structured Wasm representation boundary.

## Workaround

The binary emitter reuses FIR's validated symbolic flow result. When a
function body has no normal fallthrough, it emits an explicit `unreachable`
before the function end. That instruction is unreachable on every symbolic
execution and gives the standard validator the required polymorphic stack.

## Upstream tracking

none

## Resolution and regression

Revision `1836ef3` makes `Fir.Wasm.Emit.Binary.encodeFunctionBody` emit the
explicit terminal `unreachable` for no-fallthrough bodies.
`integration/talos/artifact/check.sh`
emits the four-module corpus twice, checks byte-for-byte reproducibility, and
uses Node's standard WebAssembly engine to validate, instantiate, execute,
and compare all four semantic observations.
