# Wasm-resident runtime audit

Status: initial complete audit on 2026-08-25. The source baseline is FIR
`631fe8e1e3cbb8e2b4893db24231011b5ac78091` with
`leanprover/lean4:v4.33.0` at Lean commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`.

This audit covers FIR's self-contained Wasm runtime: the semantic LCNF runtime
operations, the resident helper implementations, their checked linker, the W6
concrete model and proof bridge, external-engine fixtures, production package
closures, and available profile evidence. It does not audit the JavaScript
adapter implementations beyond the ownership contract they impose on the
runtime.

## Outcome

The runtime is a credible experimental execution substrate, not yet a proved
drop-in implementation of Lean's runtime.

Its strongest properties are structural:

- resident linking is explicit and fail-closed;
- complete packages own their memory and currently reach zero function and
  memory imports;
- the 23 semantic `RuntimeOp` forms have an unusually detailed concrete model,
  failure classification, and W6 operation-level coverage matrix;
- standalone V8 fixtures exercise almost every checked helper family, while
  real prettyM, Illuminate, Verso, and lean-zip packages exercise broad linked
  closures; and
- recent Array, ByteArray, String, constructor, cache, and reference-count
  work follows upstream Lean's uniqueness and ownership algorithms rather than
  replacing them with value-only approximations.

The main limitation is that syntactic closure is ahead of semantic closure.
Zero imports proves that no host function remains; it does not prove that each
installed helper implements its Lean or W6 contract. The W6 roadmap still
names the per-helper implementation theorem (T5) and import-closure theorem
(T6) as open composition layers. There are also confirmed target-safety,
fault-observation, reuse-validation, and target-width boundaries described
below.

## Architecture and comparison boundary

[`Fir/Wasm/ABI.lean`](../../Fir/Wasm/ABI.lean) defines 23 semantic runtime
operations. [`ResidentLinker.Step`](../../Fir/Wasm/Emit/ResidentLinker.lean)
defines 40 ordered linking steps because external families such as arbitrary
precision arithmetic, strings, arrays, ByteArrays, floats, and platform
operations are larger than the primitive LCNF operation set. The generic
closed-application policy selects at most 30 steps: 15 physical common steps
and 15 capability-sensitive external families.

The linker checks the symbolic module at entry and exit, rejects duplicate or
incompatible strict/available/trusted modes, requires module-owned memory,
requires no unresolved `RuntimeOp`, and normally requires zero imports. Public
exports are pruned and then compared exactly. This is the correct default
shape for a compiler runtime boundary.

FIR does **not** reproduce Lean's native heap layout byte-for-byte. The W6
model uses a 32-byte header and eight-byte semantic slots in
[`Fir/Wasm/Concrete/Layout.lean`](../../Fir/Wasm/Concrete/Layout.lean), while
upstream Lean uses its compact target-native header and native pointer-sized
payloads. FIR also deliberately retains 64-bit `USize` semantics on wasm32,
under the name `wasm32-lean64`.

Consequently, “upstream-shaped” means that allocation, uniqueness,
copy-on-write, reference-count, closure-application, and container algorithms
have the same observable behavior. Physical correspondence is instead proved
against FIR's W6 layout. The upstream reference for this audit is Lean 4.33's
[`lean.h`](https://github.com/leanprover/lean4/blob/v4.33.0/src/include/lean/lean.h),
[`object.cpp`](https://github.com/leanprover/lean4/blob/v4.33.0/src/runtime/object.cpp),
and [`apply.cpp`](https://github.com/leanprover/lean4/blob/v4.33.0/src/runtime/apply.cpp).

## Family matrix

“Executable” means a standalone V8 fixture or a production-package
differential exists. “W6” describes the strongest current proof boundary, not
the older status string embedded in a W7 manifest.

| Family | Executable coverage | W6 boundary | Audit result |
| --- | --- | --- | --- |
| Memory and allocation | Standalone memory/allocator artifacts, package frontier checks, deterministic regeneration | Linear-memory reads/writes, header construction, frontier extension, allocator implementation | Sound arena model under explicit wasm32 capacity. Released objects are marked dead; their bytes are not returned to the bump allocator. Reclamation therefore occurs through scratch rewind or instance disposal, not ordinary `dec`. |
| Headers, projections, and mutation | Checked projection/setter/tag fixtures plus mixed source corpus | Exact live/stale reads, writes, frames, packed scalar bits, source/target faults | Broad. Constructor-arity fault classification and uninitialized packed-scalar projection remain confirmed gaps. |
| Constructors | Standalone constructor artifact and real package closures | Tagged/nonempty allocation and compiler-shaped composition | Strong functional coverage. Per-layout helpers remain numerous; allocation is the leading measured prettyM family. |
| Closures and partial application | Allocation/projection/matching fixtures and real closure-heavy packages | Allocation, descriptors, capture ownership, generated matching fold, saturated and underapplied calls | Broad but not closed: `.tagged` partial-application results and some proof-indexed application/admission cases remain open. |
| Reference counting and recursive release | Increment/release artifacts, recursive graphs, source differential corpus | Complete concrete recursive success/fault theorems; installed production decrement branches are proved incrementally | Semantics are strong, but exhaustive installed last-reference composition is still W6 work. Finite `UInt32` reference-count headroom is an explicit unresolved target-safety premise. |
| Reset and reuse | Dedicated unique/shared and capacity fixtures | Fresh/in-place reuse, capacity transport, many effect frames | The concrete runtime is intentionally strict. Validator-wide preservation of retained-token ordinaryness and result-kind provenance remains open; do not widen admission around those invariants. |
| Lazy cache and persistence | Miss/hit/persistence artifacts and repeated production calls | Recursive graph persistence, global publication, hit/miss composition | Production lazy semantics are the right design. The eager persistent-cache initializer is correctly isolated as diagnostic-only and must remain out of production policies. Scratch rewind must use the cache-aware floor. |
| Nat, Int, boxes, fixed width, and `USize` | Small, 64-bit, multi-limb, conversion, zero-divisor, and lean-zip production differentials | Concrete canonical representations and selected resident arithmetic helpers | Multi-limb execution is real, not a JS fallback. Generic helper-to-concrete proofs remain incomplete. `wasm32-lean64` differs intentionally from target-native wasm32, and reference/address capacity premises remain visible. Float boxing is outside the current semantic box family. |
| Array | Checked and trusted-`set` standalone artifacts plus production clients | Allocation/copy/mutation and typed admission theorems | Uniqueness, copy-on-write, replacement ownership, equal-index swap, and borrowed/owned get paths align with upstream. Recoverable native panic observations are still omitted on checked out-of-bounds paths. The isolated trusted artifact exercises only the selected caller path, not every trusted helper. |
| ByteArray | Large checked standalone fixture and lean-zip production packages | Layout/admission work exists; trusted production proof requests remain open | Unique/shared update behavior is covered well in execution. Production uses the trusted family, but there is no standalone trusted ByteArray artifact analogous to trusted Array; this is the clearest executable-coverage gap. |
| String | Standalone UTF-8 fixture, prettyM and Verso packages | Canonical UTF-8 allocation/heap theorems and literal compiler composition | Ownership and unique-update discrepancies are fixed. The complete operational helper family still lacks a single implementation-to-concrete theorem inventory. |
| Float, platform, and libm | Raw-bit scalar fixtures, source Float cases, linked standard-libm packages | Concrete raw-bit lanes and selected conversion boundaries | Core transport preserves binary64 bits. Math packages state a platform-libm special-value/bounded-error contract, not bit-identical host-libm behavior. `System.Platform` intentionally reports the `wasm32-lean64` contract. |
| Fallbacks | Standalone artifact asserts traps; prettyM asserts both paths are absent from its trace | No semantic implementation proof | `panicCore` is plausibly fail-closed. Replacing `instInhabitedOfMonad._redArg` with `unreachable` is wrong when reachable and is now tracked by `FIR-BUG-wasm-none-generic-inhabited-fallback-trap`. |
| Linker, DCE, and tail calls | Deterministic artifact regeneration, exact import/export checks, source stress cases | Symbolic validation and separate tail-call correctness work | Fail-closed policy is a strength. Capability availability must not be confused with semantic proof; legacy bounded helpers that are shadowed by full families should be retired or named explicitly. |

The detailed operation-level proof status remains in
[`integration/talos/W6-COVERAGE.md`](../../integration/talos/W6-COVERAGE.md).
That file is substantially more accurate than helper-manifest strings such as
“generation-only; W6 proof pending,” several of which now lag behind landed W6
theorems.

## Production closure and cost evidence

The accepted prettyM Wasm identity used here is:

- 83,996 bytes;
- SHA-256 `fc61301d946b1596ad08c9b20d51d2e1f68d60ca0c04b0f9d56e298c2ec6408d`;
- zero function imports and zero memory imports; and
- 314 final functions in the exact-function sidecar whose SHA-256 is
  `ff31d65ff0d9daddfe96b47ef1f9116b8777c98eea26fc816e232d4871e72cd2`.

The sidecar classifies 46 retained Lean functions with 28,368 body bytes and
268 resident helpers with 46,251 body bytes. Resident helpers are therefore
85.4% of final functions and 62.0% of indexed function-body bytes for this
small source closure.

The accepted lean-zip raw package demonstrates why this must be measured per
consumer. Its 366,826-byte module contains 226 Lean functions with 308,041
body bytes and 275 resident helpers with 49,471 body bytes. Resident helpers
are 54.9% of functions but only 13.8% of indexed body bytes. A global runtime
size number would obscure both cases.

The current exact prettyM profile places resident allocation at a median
45.65% of Wasm self samples, reference counting at 18.78%, and retained Lean
source at 14.09%. Constructor-helper bodies have already fallen by 41.3% and
the complete module by 4.02% relative to the exact constructor experiment
baseline. Further constructor work should therefore reduce semantic allocation
count, share common allocation structure, or improve representation; more
padding removal is unlikely to address the measured cost.

Reference counting and allocation are related but distinct costs. A
constructor calls the bump allocator for a fresh object. `fir_dec_once`
maintains Lean ownership, recursively releases children, and makes uniqueness
optimization sound, but does not return the dead allocation to a free list.
This is suitable for the current whole-call scratch arenas and instance-drop
ownership model. It would need reassessment for an indefinitely lived player
without bounded rewinds.

## Confirmed semantic and safety backlog

The audit did not duplicate existing cards. The highest-impact active items
are:

1. `FIR-BUG-wasm-none-generic-inhabited-fallback-trap`: a new reachable
   semantic mismatch in the generic fallback family.
2. `FIR-BUG-wasm-none-finite-trace-refcount-overflow`: source `Nat` reference
   counts do not by themselves supply finite-header headroom.
3. `FIR-BUG-wasm-none-usize-target-width-contract`: `wasm32-lean64` is coherent
   but observably differs from Lean's target-native wasm32 runtime.
4. `FIR-BUG-wasm-none-reuse-retained-token-ordinary` and
   `FIR-BUG-wasm-none-reuse-retained-result-kind`: the reuse validator must
   preserve or invalidate its provenance facts compositionally.
5. `FIR-BUG-wasm-none-array-panic-observation`: checked Array fallbacks return
   the right values and ownership but omit Lean's recoverable panic event.
6. `FIR-BUG-wasm-none-unreachable-fault-classification`,
   `FIR-BUG-wasm-none-constructor-arity-fault-classification`, and
   `FIR-BUG-wasm-none-uninitialized-scalar-projection`: exact failure
   correspondence is not closed for every operation accepted by the linker.
7. `FIR-BUG-wasm-none-partial-apply-tagged-result`: closure result admission
   still has a representation hole.

These are not evidence that current accepted package corpora are failing. They
are the boundaries that prevent upgrading broad differential evidence into a
generic runtime-correctness claim.

## Coverage gaps

The existing artifact gate is broad: it emits and runs standalone artifacts
for memory, allocator, checked Array, trusted Array set, checked ByteArray,
fixed width, Float, linked libm, constructors, closures, boxes, literals,
mutation, reference counts, cache, numeric/BigNumeric/Nat arithmetic,
platform, String, fallbacks, tags, and projections. It also regenerates source
artifacts twice and compares exact bytes and sidecars.

The following gaps should be closed without building a second harness:

1. Add a `resident-byte-arrays-trusted` command and client mode to the existing
   artifact gate. Reuse the checked corpus, mark malformed-layout cases as
   checked-only, and assert that all semantic ownership/capacity/overflow cases
   agree between checked and trusted bodies.
2. Extend the trusted Array standalone client from the selected `Array.set`
   caller to every trusted helper selected by the generic production policy.
3. Add one reachable native/Wasm differential for the inhabited fallback.
4. Keep a manual per-family W7 implementation/W6 theorem table in this audit
   until T5 exposes a stable theorem API. Do not infer proof status from W7
   manifest prose and do not add a coordination daemon.
5. Keep consumer packages as integration coverage. Do not move their workload
   or oracle catalogs into FIR; record only immutable artifact identities and
   results here.

## Recommended sequence

1. Make generic fallback linking semantically honest: compile/reuse Lean's real
   inhabited implementation or reject a reachable retained declaration.
2. Add the isolated trusted ByteArray and expanded trusted Array executable
   checks, then send their exact premises to W6.
3. Finish the installed recursive-release T5 stack and close the already-open
   trusted container proof requests before broadening admission.
4. Move finite address/refcount headroom into one explicit target-safety
   boundary, keeping it separate from compiler validation.
5. Replace stale per-helper proof-status strings with a reference to the W6
   coverage matrix or a reviewed static table; do not create another generated
   coordination system.
6. Retire or explicitly label compatibility-only bounded helpers such as the
   old standalone `ResidentNatMod` path when the full arbitrary-precision
   family always shadows them in production.
7. Resume allocation consolidation only after the first four correctness
   items are either closed or kept outside the candidate's contract. Use exact
   package sidecars and checked profiles, not a shared global runtime number.

## Audit completion criterion

The runtime can be called generically correct for a supported closed source
fragment when:

- every selected resident helper has an implementation-to-W6 theorem;
- every accepted source failure has exact or explicitly versioned observable
  target behavior;
- target-only failures are excluded under stated finite memory and reference
  count premises;
- trusted helper premises are derived from compiler validation and exercised
  independently in a real engine;
- final import closure is connected to those theorems, rather than checked
  only as module syntax; and
- the same immutable package passes native, semantic-host, V8, browser, and
  consumer differential checks.

Until then, package claims should remain precise: self-contained,
zero-import, externally differential-tested on a named corpus, with a stated
`wasm32-lean64` layout and ownership contract.
