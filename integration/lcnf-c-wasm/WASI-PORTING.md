# WASI support policy

The WASI Preview 1 reactor is an experimental compatibility profile for the
LCNF-to-C lane. ABI 3 is frozen at its current surface while Emscripten remains
the primary full-runtime target.

The freeze keeps the existing artifact and tests useful without placing
incremental WASI runtime work on the short-term critical path.

## Frozen ABI 3 boundary

ABI 3 admits the runtime behavior exercised by `Smoke.lean`,
`HeapSmoke.lean`, `WasiCoreSmoke.lean`, and `WasiScalarSmoke.lean`:

- scalar functions and tail loops;
- boxed `UInt64` values and constructors;
- single-threaded reference counting and stack-safe reclamation;
- ordinary object arrays, byte arrays, and strings;
- fully applied `apply_1` and `apply_2` calls through arity three;
- WASI Preview 1 clocks plus wasi-libc reactor initialization.

It continues to fail closed on partial or unadmitted closure application,
non-byte scalar arrays, structure arrays, tasks, thunks, references, external
objects, multi-threaded reference counts, and `Init`/`Std` host services.

ABI 3 may receive correctness, security, toolchain-compatibility, and test
hardening changes. New object kinds, closure modes, host services, or imports
are surface expansion and require a new reviewed ABI rather than silently
changing ABI 3.

## When to resume WASI expansion

Expansion should resume only when at least one of these conditions holds:

1. a concrete deployment requires a non-JavaScript WASI host;
2. an agreed representative workload cannot use the frozen surface;
3. a selective upstream Lean runtime port demonstrably reduces the
   lane-maintained ABI implementation.

Until then, realistic programs use Emscripten and pure kernels may use the
freestanding profile.

## Selective upstream port

The preferred future direction is a partial source port, not continued
function-by-function reimplementation:

```text
generated Lean C
  + upstream portable Lean allocation/object/apply sources
  + a small WASI host adaptation layer
  -> LLVM `-O3` plus full LTO
  -> WASI reactor
```

The first bounded experiment should:

1. compile only the upstream runtime translation units needed by the current
   fixtures with the pinned wasi-sdk;
2. enumerate unresolved platform dependencies instead of adding stubs
   opportunistically;
3. keep tasks, threads, libuv, networking, processes, and full `Init`/`Std`
   outside the experiment;
4. pass the existing native-runtime and JavaScript differential oracles,
   per-object-kind reclamation checks, and zero-live-object checks;
5. report artifact size, imports, and throughput against the frozen ABI 3
   implementation.

Link-time optimization and section garbage collection should determine the
reachable runtime cone. The experiment is successful only if it replaces
material bespoke runtime code without weakening correctness or expanding the
host contract accidentally.
