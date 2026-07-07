# FIR research notes

## Lean compiler IR status

Lean currently has two relevant compiler IR layers.

The primary compiler pipeline is centered on `Lean.Compiler.LCNF`. `Lean.Compiler.Main`
calls `LCNF.main`, the pass manager runs base/mono/impure LCNF phases, and the C emitter
operates directly on impure LCNF.

The older lower `Lean.IR` layer still exists. It defines `IRType`, `Expr`, `FnBody`, and
`Decl`, and the LCNF pipeline still lowers impure LCNF to `Lean.IR` with `IR.toIR` before
calling `IR.compile`. This lower layer is still useful for interpreter metadata and the
LLVM-facing code path, but it is not the best v1 anchor if the goal is to track the current
compiler.

## Master drift check

I checked upstream `lean4` master at commit `9b4f465` from 2026-07-06 against the installed
Lean 4.31.0 toolchain in this environment.

The files `Lean.Compiler.IR.Basic`, `Lean.Compiler.IR.ToIR`, and `Lean.Compiler.IR.Checker`
were byte-identical between Lean 4.31.0 and that master checkout. `Lean.Compiler.LCNF.Basic`
had only a small unrelated change around reducibility queries.

The important drift is architectural rather than syntactic: LCNF is the compiler-centered IR,
while lower `Lean.IR` remains a lower layer.

## Existing semantics and checks

Upstream Lean provides structural and type-shape checkers for compiler IRs, not a full
mechanized operational semantics or compiler-correctness theorem for LCNF or lower `Lean.IR`.

The LCNF checker validates local context shape, application types, branch/case structure,
join-point arity, and uniqueness properties. The lower `Lean.IR` checker validates variables,
join points, object/scalar expectations, constructor runtime limits, and application arity.

The closest paper background for the lower reference-counting IR is "Counting Immutable Beans".
LCNF itself is A-normal-form-inspired compiler infrastructure with explicit pure and impure
phases.

## WebAssembly in Lean

The official WebAssembly spec gives the baseline execution semantics and a reference
interpreter. The current online core spec is WebAssembly 3.0 dated 2026-06-25.

Lean projects found during research:

- Talos (`cajal-technologies/talos`): Lean 4.31.0, executable Wasm semantics, examples, and
  WP/spec predicates. This is the best candidate for a future FIR-to-Wasm bridge.
- Wean (`pmatos/wean`): useful WebAssembly 3.0 runtime/equivalence reference, but pinned to
  Lean 4.27.0-rc1 in the inspected checkout.
- `aionescu/lean-wasm`: a small intrinsically typed interpreter and useful design reference,
  but its proof-carrying evaluator still has unfinished proof placeholders.

## V1 formal model

V1 formalizes a deliberately tiny impure LCNF subset:

- let-bound literals,
- erased values,
- variable return,
- unreachable,
- unsupported-operation rejection.

This gives a stable executable evaluator, a matching big-step relation, and trivial theorems
that can be used to evaluate future proof ergonomics before adding heap, reference counting,
constructors, calls, or Wasm simulation.

## Compiler-emitted LCNF observations

`lake lean Inspect` now compiles a few local declarations through `LCNF.main` and reads the
local impure declaration extension with `getLocalImpureDecl?`.

With Lean 4.31.0, the emitted shapes and coverage report are already informative:

- A literal `Nat` definition becomes a literal let followed by `return`.
- Identity on `Nat` uses a borrowed parameter (`@&x`), then `inc x`, then `return x`.
- Branching on `Bool` emits `cases` with literal-return branches.
- First projection from `Nat × Nat` emits `oproj[0]`, then `inc`, then `return`.

Current generated coverage:

```text
litNat: params=0, borrowed=0, code-supported=yes, call-ready=yes, first-unsupported=-
idNat: params=1, borrowed=1, code-supported=yes, call-ready=no, first-unsupported=-
branchNat: params=1, borrowed=0, code-supported=no, call-ready=no, first-unsupported=cases
pairFirst: params=1, borrowed=1, code-supported=no, call-ready=no, first-unsupported=oproj
```

The `inc` instruction is now modeled as an observational no-op in the FIR evaluator. That
makes the body of `idNat` supported, while the declaration is still not call-ready because
we do not yet bind declaration parameters to argument values.

This suggests the next semantic increments should be declaration-parameter/argument binding,
constructor cases, and object projection. Full heap layout, destructive update, closures, and
precise reference-counting soundness should still wait.

## Next bridge target

The next milestone should relate this LCNF subset to Wasm observations, probably through Talos
rather than raw Wasm syntax or binary parsing. The initial relation should compare return-value
observations for straight-line code before modeling heap layout, Lean runtime imports, reference
counting, closures, or constructors.
