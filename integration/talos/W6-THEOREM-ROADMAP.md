# W6/W7 theorem roadmap

This document states the proof obligations for the concrete WebAssembly lane.
The operation inventory in `W6-COVERAGE.md` records which local runtime rules
exist; this roadmap records the program theorems those rules must build.

The boundaries here are intentionally allowed to evolve. Clients may
experiment against them, but should expect to adapt when a cleaner statement
or representation makes a proof substantially better.

## Semantic endpoints

The successful source endpoint is FIR's executable final-impure LCNF
semantics:

```lean
ExecEvaluates sourceExternals
  (sourceCodeState context sourceRuntime sourceEnv sourceCode)
  (ReturnedObservation resultRuntime resultValue)
```

The successful target endpoint is Talos's fuel-free total-correctness
predicate over the W6 concrete host:

```lean
Wasm.TerminatesWith hostEnv module functionIndex initial arguments
  (RefinedReturnPost resultRuntime resultValue resultKind callerTail)
```

`RefinedReturnPost` must state all of the following:

1. the concrete run returns exactly one physical value and preserves the
   caller operand tail;
2. the final concrete runtime refines `resultRuntime` under some
   `RefinementWitness`;
3. the structured concrete failure channel is clear; and
4. the physical result refines `resultValue` at `resultKind`.

`ConcreteRuntimeRel` already includes heap, globals, world, and trace. The
public success theorem therefore does not need a second observation relation
that could silently omit part of the runtime.

## The theorem ladder

### T1. Successful declaration certificate

`SuccessfulDeclaration` is the first public concrete theorem boundary. Its
hypotheses package:

- a finite successful source execution;
- the exact generated function index and non-import/function-lookup facts;
- a compiler-and-adapter `CodeWP` for the generated body;
- the initial concrete/source state relation carried by that `CodeWP`;
- an exact final target store and physical result;
- `ConcreteRuntimeRel` for the final source runtime;
- a clear concrete failure channel; and
- `PhysicalValueRel` for the returned source value.

Its main consequence is source termination paired with concrete target
termination under `RefinedReturnPost`. A second, stronger consequence retains
the exact final store and physical value for callers such as lazy-cache
publication.

The body judgment is parameter- and caller-tail-polymorphic. A declaration
with physical parameters `parameters` is proved once, and the theorem applies
to every caller operand remainder:

```lean
parameters.length = targetFunction.numParams
∀ callerTail,
  CodeWP ... targetFunction.body ...
    (ConcreteFunctionBodyPost targetFunction (parameters ++ callerTail)
      (ExactReturnPost afterCall physical callerTail))
```

For a nullary declaration, this entails the existing
`CachedDeclarationBodyWP`; cache correctness is a corollary of declaration
correctness rather than the public semantic specification.

T1 is a sound certificate theorem. It deliberately does **not** claim that
successful source evaluation alone implies target correctness.

### T2. Syntax-directed concrete simulation

The main W6 compiler proof is an inductive `ConcreteCodeSimulation`, analogous
to the semantic-host `Correctness.CodeSimulation`, but indexed by concrete
stores and refinement witnesses. It must have constructors for:

- return;
- direct value `let`;
- object and scalar cases;
- no-result effects;
- direct and closure calls;
- external calls; and
- lazy-cache hit and miss paths.

The induction must prove both:

```lean
ConcreteCodeSimulation ... → CodeWP ...
ConcreteCodeSimulation ... → ExecEvaluates ...
```

and then construct `SuccessfulDeclaration`. Existing W6.6 operation
composition theorems are intended to discharge its step premises. T2 is the
point at which local operation coverage becomes a compiler correctness
theorem.

### T3. Whole-export success

`ConcreteSupportedExport` must package only static whole-pipeline evidence:

- `WasmSupported`;
- successful `lowerSupported`;
- source-function lookup;
- successful Talos adaptation;
- successful concrete-host resolution;
- exported-name/function lookup; and
- the single-result ABI.

Combining `ConcreteSupportedExport` with `ConcreteCodeSimulation` must yield:

```lean
ExecEvaluates ... observation ∧
ConcreteExportTerminatesWith ... (RefinedReturnPost ...)
```

This theorem must use the exported function selected from the generated
module, not a hand-written body or fixture-specific index.

### T4. Structured faults

Fault correctness is a separate theorem, not a disjunct hidden inside T1:

```lean
source reaches sourceError
→ concrete target terminates in the corresponding structured failure
```

The relation is `ConcreteErrorSourceRel`. The proof must retain operation and
precedence information, including stale-object, bounds, malformed-layout,
allocation, and external failures. A target trap without the related
structured source error does not satisfy this theorem.

### T5. Wasm-resident runtime linking

W7 replaces concrete host functions with Wasm-resident implementations over
`WebAssembly.Memory`. For each currently concrete-resolved `RuntimeOp`, prove:

```lean
internalRuntimeFunction implements concreteHostFunction
```

The linking theorem then replaces calls to concrete runtime imports by calls
to those internal functions while preserving T3's result. This theorem is the
proof boundary between W6's concrete-runtime semantics and W7's generated
self-contained artifact.

JavaScript implementations remain useful executable oracles, but are not the
implementation quantified over by T5.

### T6. Import closure

After linking, inspect the final module and prove that every remaining function
import corresponds to a genuine source external. Consequently, a pure source
program has no function imports:

```lean
source program has no externals
→ linkedModule.functionImports = []
```

For the pure `prettyM` target, the artifact acceptance criterion is:

- zero function imports;
- exported linear memory and the agreed low-level construction operations;
- agreement with the existing Node, Chrome, and native-oracle tests; and
- the T3 result transported through T5.

## Completion criteria

W6 program correctness is complete when:

- T1 is implemented and used as the common declaration boundary;
- T2 covers every operation admitted by the supported fragment;
- T3 is proved without fixture-specific compiler or layout assumptions;
- T4 covers every structured failure admitted by that same fragment; and
- direct recompilation, `make check`, and `make talos-check` are green.

W7 self-containment is complete when T5 covers every concrete runtime import
used by the target, T6 establishes the import claim, and the external-engine
acceptance tests pass.

## Work order

1. Implement T1 and derive the existing nullary cache package from it.
2. Introduce the return/direct-let spine of `ConcreteCodeSimulation`.
3. Add case constructors by consuming the existing W6.6 step theorems; effect,
   call, external, and lazy constructors are now present.
4. Package the whole generated export as T3.
5. Build the fault induction T4 in parallel with remaining success
   constructors.
6. Let W7 generation proceed independently against the current concrete
   runtime surface, then prove T5 per internalized runtime function.
7. Close with T6 and the pure `prettyM` acceptance theorem.
