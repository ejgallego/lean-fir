# From LCNF to C in Lean 4.32.0

This document describes the Lean compiler pipeline relevant to FIR, from an
elaborated declaration through LCNF and into generated C. It is based on the
Lean 4.32.0 toolchain pinned by this repository.

There is an important naming and architectural distinction:

- `Fir.LeanIR.Impure` is FIR's reference semantics for final impure LCNF. It
  does not run compiler passes or emit C.
- `Fir.LeanIR.Legacy` is the original small evaluator retained only as a
  differential fixture.
- The upstream Lean compiler runs the passes described below. FIR's `Inspect`
  entrypoint invokes that pipeline and observes its final impure LCNF output.

The overall flow is:

```text
Elaborated kernel expression
        | toDecl / toLCNF
        v
Pure base LCNF
        | base optimization passes
        v
Pure monomorphic LCNF
        | mono passes and SCC splitting
        v
Impure, runtime-aware LCNF
        | ownership and memory-management passes
        v
Final saved impure LCNF ------------> Direct C emitter ---> C source
        |
        `---> Lean.IR.toIR ---> legacy IR/interpreter/LLVM infrastructure
```

The normal C emitter consumes final impure LCNF directly. `Lean.IR.toIR` is a
parallel side branch, not an intermediate representation on the C-emission
edge.

## Creating base LCNF

`toDecl` takes an elaborated Lean declaration, and `toLCNF` puts its
computationally relevant expression into A-normal form. For example, an
expression of the shape

```lean
f (g x)
```

becomes conceptually:

```text
let y := g x
let z := f y
return z
```

Proofs and type-only information are erased or represented specially. The
result is `LCNF.Decl .pure`: it is still high-level and polymorphic, with local
functions, applications, projections, and cases.

## Base passes

The base passes run in the following order.

1. **`init`** registers the initial declarations and establishes the first
   checked snapshot.
2. **`pullInstances`** hoists type-class instance computations and dependent
   projections to wider scopes where possible.
3. **`cse`** performs common-subexpression elimination.
4. **`simp`** applies the main LCNF simplifier: inlining, local reductions,
   projection and case simplification, eta transformations, and related
   cleanup.
5. **`floatLetIn`** moves a `let` into the particular case branch where it is
   used, avoiding work in other branches.
6. **`findJoinPoints`** recognizes local functions used only as control-flow
   destinations and changes them into `jp`/`jmp` join points.
7. **`pullFunDecls`** hoists local functions and join points as far outward as
   their dependencies permit.
8. **`reduceJpArity`** removes unused join-point parameters and corresponding
   jump arguments.
9. A second **`simp`** enables polymorphic eta processing, partial-application
   inlining, and `@[implemented_by]` replacement before specialization.
10. **`eagerLambdaLifting`** lifts selected local functions that depend on
    type-class instances so specialization can see them.
11. **`checkTemplateVisibility`** ensures specialization and inline templates
    refer only to bodies available at the appropriate module boundary.
12. **`specialize`** generates specialized declarations when arguments,
    especially instances or other static values, are known.
13. A second **`findJoinPoints`** discovers opportunities created by
    specialization.
14. A third **`simp`** cleans up the specialized result.
15. A second **`cse`** removes newly duplicated expressions.
16. **`saveBase`** stores normalized base LCNF.
17. **`inferVisibility`** determines which compiler bodies must remain visible
    across modules.
18. **`toMono`** removes universe and type parameters, erases irrelevant
    arguments, maps types to runtime-oriented monomorphic types, and rewrites
    special built-in cases.

## Monomorphic passes

At this stage LCNF remains `.pure`: memory ownership and reference counting
are still implicit.

1. **`simp`** simplifies the initial monomorphic form.
2. **`reduceJpArity`** removes unused join-point parameters again.
3. **`structProjCases`** rewrites projections from single-constructor
   structures into case-bound fields, allowing projections and nested cases
   to be combined.
4. **`extendJoinPointContext`** makes values captured by join points explicit
   in their parameter context.
5. **`floatLetIn`** moves computations into the branches that need them.
6. **`reduceArity`** creates reduced-arity versions of functions with unused
   parameters.
7. **`commonJoinPointArgs`** removes join-point arguments that are identical
   across all jumps.
8. Another **`simp`** cleans up the reduced functions and join points.
9. Another **`floatLetIn`** exploits the simplified control flow.
10. **`lambdaLifting`** eliminates all remaining local functions by creating
    top-level auxiliary declarations.

The compiler then splits the declaration group into strongly connected
components. For each component it runs:

11. Another **`extendJoinPointContext`**.
12. Another **`simp`**.
13. **`elimDeadBranches`**, which uses abstract interpretation to remove
    constructor branches proven unreachable.
14. **`cse`**.
15. **`saveMono`**, which stores normalized monomorphic LCNF.
16. **`inferVisibility`** for the mono phase.
17. **`extractClosed`**, which extracts strings, large literals, arrays, and
    other closed values into separate declarations.
18. **`toImpure`**, which transitions to runtime-aware LCNF.

## Transition to impure LCNF

`toImpure` introduces concrete runtime representation distinctions:

- object versus tagged-object values;
- machine scalars and `usize` values;
- erased and void values;
- full versus partial applications;
- constructor layout information; and
- object, scalar, and `usize` projections: `oproj`, `sproj`, and `uproj`.

The IR now has enough information to express allocation, mutation, borrowing,
and reference counting.

## Impure passes

1. **`pushProj`** pushes projections into the case arms that actually need
   them.
2. **`resetReuse`** detects when a dead constructor object can be reused
   for a subsequent allocation and inserts abstract `reset`/`reuse`
   instructions.
3. **`elimDeadVars`** removes unused bindings when doing so is safe in an
   effectful IR.
4. **`simpCase`** removes unreachable arms and combines equivalent case arms
   after reuse analysis no longer needs the original case structure.
5. **`inferBorrow`** chooses borrowed versus owned parameters for functions
   and join points, determining whether calls consume references.
6. **`explicitBoxing`** inserts `box`/`unbox` operations and creates boxed
   wrapper functions for closures and interpreter-facing calls.
7. **`explicitRc`** performs liveness and ownership analysis and inserts
   explicit `inc` and `dec` instructions.
8. **`expandResetReuse`** converts abstract reset/reuse into explicit
   shared-versus-exclusive control flow, allocation, mutation, and deletion
   operations.
9. **`coalesceRc`** combines repeated `inc` or `dec` operations on the same
   value within a basic block.
10. A second **`pushProj`** optimizes projections around cases introduced by
    reset/reuse expansion.
11. **`detectSimpleGround`** recognizes values that can be emitted as static C
    initializers rather than allocated during module initialization.
12. **`inferVisibility`** records final visibility information.
13. **`toposort`** orders declarations so constants and closed terms can be
    emitted in dependency order.
14. **`saveImpure`** normalizes and records the final impure declarations
    consumed by downstream emitters.

## Emitting C

`LCNF.emitC` reads the declarations recorded by `saveImpure` and emits:

- C headers and runtime imports;
- function prototypes and bodies;
- static ground objects;
- module runtime and compile-time initialization functions; and
- a `main` wrapper when appropriate.

Representative translations include:

- constructors to `lean_alloc_ctor` and field setters;
- projections to `lean_ctor_get` and scalar variants;
- partial applications to closure allocation;
- `inc` and `dec` to Lean runtime reference-counting calls;
- `cases` to C branches or switches;
- object updates to Lean runtime setters; and
- `return` to a C return.

Lake subsequently invokes the platform C compiler to produce object files and
link them against the Lean runtime.

## Using C as a WebAssembly backend

FIR's compiler-native Wasm path preserves this upstream edge: final impure
LCNF is emitted as C first, then Emscripten/LLVM compiles and links that C with
the pinned Lean runtime, `Init`, and `Std`. The result is a verified
`.manifest.json`/`.mjs`/`.wasm` deployment bundle for Node and
cross-origin-isolated browsers.

This is separate from FIR's symbolic Wasm path. That backend consumes the same
final impure LCNF but lowers it through `Fir.Wasm`, where instructions,
semantic imports, resident-runtime helpers, and W6/W7 refinement obligations
remain explicit. Sharing the source checkpoint supports differential
validation; it does not imply a shared runtime ABI or artifact loader.

See the [WebAssembly artifact-generation guide](wasm-artifact-generation.md)
for the comparison and the
[LCNF-to-C package](../integration/lcnf-c-wasm/README.md) for reproducible
toolchain pins, optimized flags, loader rules, and acceptance checks.

## The parallel lower-IR branch

After the impure passes, `LCNF.Main` also invokes `Lean.IR.toIR` followed by
`Lean.IR.compile`. This translates final impure LCNF into Lean's older lower IR
and records it for interpreter, metadata, and LLVM-related uses.

This lowering currently runs before the frontend asks `LCNF.emitC` for the C
source, but it does not feed the C emitter. Both consumers read from the final
impure LCNF result.

## Where FIR attaches

`Inspect.compileAndReportImpureDecl` calls the complete `LCNF.main` pipeline and
then retrieves the declaration saved by `saveImpure`. The LCNF printed by FIR
is therefore essentially the same representation consumed by `emitC`.

`Fir.LeanIR.Impure` provides the reference machine for that final
representation. It models the complete final-impure instruction grammar,
including control flow, calls and closures, heap mutation, external effects,
and reference-count operations. For example, final LCNF for an identity
declaration contains:

```text
inc x
return x
```

The new FIR machine changes the abstract heap reference count for `inc`; the C
emitter turns it into the corresponding Lean-runtime operation. Relating that
abstract heap model to a concrete runtime implementation is a proof obligation
for both C and Wasm. The isolated `Fir.LeanIR.Legacy` evaluator remains as a
small differential baseline and does treat `inc` as observationally invisible.

## Source locations

The most relevant sources in the pinned Lean toolchain are:

- `Lean/Compiler/LCNF/ToDecl.lean` and `ToLCNF.lean` for initial conversion;
- `Lean/Compiler/LCNF/Passes.lean` for the exact pass ordering;
- `Lean/Compiler/LCNF/Main.lean` for pipeline orchestration;
- `Lean/Compiler/LCNF/ToImpure.lean` for representation lowering;
- `Lean/Compiler/LCNF/EmitC.lean` for direct C emission; and
- `Lean/Compiler/IR/ToIR.lean` for the parallel lower-IR branch.

Within FIR, see `Inspect` for final-LCNF extraction,
`Fir/LeanIR/Interpreter.lean` for the reference machine, and
`Fir/LeanIR/Legacy.lean` for the differential baseline.
