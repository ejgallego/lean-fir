# FIR verification roadmap

This is the live repository-wide verification roadmap for the Lean 4.33.0
pipeline pinned by FIR. Detailed landed-proof chronology is archived in
[`pass-correctness-history.md`](pass-correctness-history.md); historical uses
of "next", "remaining", or "immediate" there, and in later chronological
sections of track plans, do not define current priority.

`docs/research.md` supplies broader rationale, `docs/lcnf-to-c.md` supplies the
compiler-pipeline reference, and `integration/talos/PLAN.md` records the W6/W7
implementation ledger. Live status combines this roadmap, commit ancestry,
the canonical local mailbox, and the accepted integration-board snapshot.
Tracked lane files are milestone handoffs, not independent backlogs.

## Current verification frontier — 2026-08-30

### Repository goal

Prove finite-prefix behavioral preservation for the actual compiler chain:

```text
earlier LCNF
    | verified pass simulations
    v
final impure LCNF
    | closed W6 compiler simulation
    v
generated Wasm under runtime contracts
    | resident-runtime linking
    v
self-contained executable Wasm
```

This is not a termination theorem and does not establish a functional
postcondition for the source program. A finite observable prefix is matched
even when the execution may continue forever.

### Critical path

1. **PA0 — admission audit.** Classify every schema-aware current-node branch
   with exact theorem dependencies in
   [`w6-source-admission-audit.md`](w6-source-admission-audit.md).
2. **PA1 — minimal semantic provenance.** Add only source facts that PA0 proves
   cannot be reconstructed from the guarded validated relation.
3. **PA2 — compiler-derived guarded admission.** Derive the current-step
   compiler admission package from production validation, the active relation,
   and one successful source step.
4. **PA3 — closed W6 theorem.** Publish an export-facing finite-prefix theorem
   with no caller-provided `SourceInvariant`, source laws, constructor schema,
   future trace, or program certificate.
5. **PA4a — one backward composition.** Precompose the nearest already-proved
   pass as an interface test.
6. **PA4b — resident linking.** Discharge contracted runtime operations through
   verified resident helpers as a distinct theorem layer.

No further backward pass hop is on the shared critical path before PA3.
New runtime features, program-specific verification of `sumTo`, a broad
`ValueInfo` redesign, unrelated pass coverage, and performance changes that
reshape shared proof contracts are not on this path.

### Definition of closed W6

The canonical export theorem:

- starts from a real compiler-produced `ConcreteSupportedExport`;
- constructs its initial validated source/target relation internally;
- constructs the initial constructor schema from the actual entry refinement;
- derives current-node admission from compiler validation and semantic
  provenance;
- contains no caller-chosen source invariant, future execution, target path,
  translation certificate, or reachability enumeration;
- retains external/runtime compatibility and finite machine-resource safety as
  explicit execution premises; and
- introduces no trusted axiom.

`ConcreteSupportedExport.finiteTraceCorrect_of_sourceInvariant` and its
schema-indexed form remain internal or compatibility layers after PA3. The
roadmap and examples then reference only the closed endpoint.

### Theorem contracts

| Milestone | Current theorem or interface | Premises to eliminate | Premises retained | Owner | Definition of done |
|---|---|---|---|---|---|
| PA0 | `ConcreteStructuredSourceAdmissionSafeAt`; `ConcreteStructuredSchemaSourceAdmissionSafeAt`; `ConcreteStructuredCodeStepAdmission` | None during audit | Existing compiler, semantic, and resource boundaries unchanged | W6 audit owner | Every target branch has exact facts, conclusion, theorem dependency, A–E class, owner, and regression; no unresolved prose |
| PA1 | Existing operation-specific source-safety and producer/result lemmas | Any caller-supplied precise-result or field-provenance fact identified as class C | Facts reconstructible locally from validation and the active relation | W6 result/object helper owners | Every class-C row is closed without a public provenance map or universal source invariant |
| PA2 | `ConcreteStructuredCompilerCurrentStepAdmission`; `ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step` | `ConcreteStructuredSchemaSourceReadyAt` as a client-provided current-node law | `ConcreteStructuredCurrentStepFiniteRuntimeSafety`; `ConcreteStructuredCurrentStepAddressSpaceSafety` | W6 owner | Production compiler facts construct current-step admission for every successful guarded source step |
| PA3 | `ConcreteSupportedExport.finiteTraceCorrect_of_schemaSourceInvariant` | `SourceInvariant`, `sourceLaws`, `sourceInitialInvariant`, caller-selected `initialSchema` | Entry relation; runtime/external contracts; finite header/capture safety; allocation headroom | W6 owner | Canonical `ConcreteSupportedExport.finiteTraceCorrect` has the closed-W6 surface and an exact axiom regression |
| PA4a | Generic finite-stuttering/pass bridge, including `precomposeStutteringPass` | Any renamed form of the W6 source-invariant premise | The earlier pass's real semantic and well-formedness hypotheses | Composition owner | One existing pass theorem yields an earlier-LCNF-to-contracted-Wasm finite-prefix theorem |
| PA4b | Helper-specific implementation-to-concrete-runtime refinements | Abstract runtime-operation implementations covered by resident helpers | External operations not yet resident; finite wasm32 resources | W6/W7 linking owners | A separately named contracted-Wasm-to-self-contained-Wasm theorem composes with W6 |
| EDV-general | `ElimDeadSourceOwnedExactContract` and strict checked endpoints | Fixture-specific source-state and target-ledger classifications | Nullary full-application exclusion; foreign-spec compatibility | LCNF proof owner | Arbitrary checked compiler entries construct mapped-owner, source-only allocation, reset/reuse, and ledger interfaces |

### Assumption budget

Compiler facts that must be derived inside the proof:

- supported export/declaration identity and residual structured validation;
- hygiene, local kinds, call signatures, result compatibility, and case
  normalization;
- the canonical initial constructor schema and active schema/witness agreement;
- exact producer result information where ABI carrier compatibility is too
  coarse;
- call, closure, cache, constructor, projection, and field provenance; and
- current-node admission plus its exact allocation cost.

Execution and resource premises deliberately retained:

- correct initial source/target runtime relation and runtime invariant;
- external and resident-operation refinement contracts;
- finite reference-count header and saturated-capture retention capacity; and
- exact allocation headroom within the current wasm32 frame budget.

Semantic exclusions and contracts kept visible:

- effectful nullary full applications remain conservatively excluded until a
  checked declaration/external contract supplies semantic purity or
  stuttering;
- address-renamed heaps require address-parametric or explicitly compatible
  foreign semantics; and
- address-space premises remain until resource exhaustion is represented as a
  matched observable outcome.

Trusted proof assumptions:

- exactly one audited Lean 4.33 upstream-to-transparent alpha-equivalence
  correspondence axiom in `AlphaEqvTrusted.lean`;
- pinned upstream source hashes checked by `make check`; and
- no W6, `elimDeadVars`, runtime-layout, or resident-helper axiom.

Resource and foreign-semantics premises are contracts, not trusted axioms.

## Parallel `elimDeadVars` lane

The LCNF lane proceeds independently of PA0–PA3 and does not edit W6 theorem
interfaces. Its next general endpoint is arbitrary compiler-produced checked
entry states, not another family of local instruction matchers.

The work order is:

1. thread durable source-only allocation through the generic ledger dispatcher
   and strong simulation;
2. derive `TargetMappedOwnerPrefix`-style ownership from arbitrary exact
   checked residual states;
3. replace remaining finite reset/reuse classifications with generic local
   operation-shape and ownership preservation lemmas;
4. reach the strict compiler-facing whole-program theorem without fixture
   enumeration; and
5. retain the conservative nullary full-application exclusion until the
   semantic constant-purity contract is resolved.

After that endpoint, resume the reverse campaign through projection movement
and later ownership/mono boundaries only when each theorem implements the
common simulation interface.

## Proof architecture that remains stable

### Three explicit LCNF phases

Lean has three named LCNF phases but two syntax purity indices:

| Phase | Underlying type | Principal invariant |
|---|---|---|
| base | `LCNF.Decl .pure` | polymorphic source structure remains |
| mono | `LCNF.Decl .pure` | polymorphism has been eliminated |
| impure | `LCNF.Decl .impure` | representation, effects, and ownership are explicit |

FIR's `Program phase` distinguishes base and mono theorem inputs even though
both use `.pure` syntax. `CheckedProgram phase` pairs a program with its phase
invariant. FIR does not maintain three duplicate AST implementations.

### Common correctness interfaces

Same-phase passes compare behavior at source entry points. Cross-phase and
backend theorems use explicit value, observation, heap-renaming, and weak-step
relations. Unreachable heap garbage may differ; observable worlds, traces,
results, faults, and reachable storage must agree under the stated relation.

Compiler proofs have two layers:

1. a semantic transformation or simulation kernel; and
2. conformance of Lean's actual compiler implementation, including generated
   names, declaration groups, validation, and environment updates.

Generic observable weak simulations, finite-stuttering pass simulations, and
finite-prefix packages already compose. Their presence is infrastructure; it
does not close W6 until compiler-derived current-node admission is available.

### Backward campaign order

`reverseProofCampaign` remains the executable source of the guarded reverse
pass order. The strategic order is final impure passes, the late-mono/impure
boundary, SCC and early-mono transformations, then base/frontend lowering.
The exact historical list and rationale are preserved in
[`pass-correctness-history.md`](pass-correctness-history.md).

## Ownership and task acceptance

Only the W6 owner edits
`integration/talos/FirTalos/ConcreteResumableWasm.lean` while PA0–PA3 are
active. Result- and object-provenance contributors add focused helper modules
or isolated lemmas and publish immutable handoffs. Shared relation, ABI,
layout, interpreter, and symbolic-Wasm changes follow the contract queue.

Before implementation, every proof task records:

1. target theorem name and intended signature;
2. the public premise it removes or discharges;
3. classification of every remaining premise as compiler, semantic, resource,
   or trusted;
4. the shared relation or theorem surface it must not redesign;
5. the condition that signals a semantic discrepancy rather than a tactic or
   elaboration failure; and
6. focused and complete validation gates.

Proof-only exit gates are:

```text
Lean Beam iteration
lake build <focused proof cone>
make check
make talos-check
git diff --check
trusted-axiom and source-hash gates
#print axioms <new public endpoint>
```

Emitter, resident-runtime, layout, ABI, or artifact changes additionally run
the complete deterministic artifact and differential gates. Gate names, not a
fixed corpus count, define acceptance.

## Trust and release closure

`simpCase`'s transparent recursive proof is mature. Its single upstream
checker correspondence axiom remains isolated and source-hash audited. The
durable resolution is an upstream equation theorem or proof-facing API,
followed by a proof of `UpstreamBridge` and removal of that axiom.

Hosted automation should eventually separate a required pull-request gate
(focused Lean build, `make check`, trust hashes, bug-card validation, exact
axiom count) from a heavyweight nightly/manual gate (Talos, deterministic
generation, artifact execution, and native/LCNF/V8 differentials). Protect
`main` only after those hosted checks are stable and required.

## Phase milestones

| Milestone | Result |
|---|---|
| M1 — Closed W6 | Final-LCNF-to-Wasm theorem without caller source invariant |
| M2 — First compiler-chain theorem | One earlier verified pass composed with W6 |
| M3 — Executable theorem | Contracted Wasm linked to verified resident helpers |
| M4 — General `elimDeadVars` | Arbitrary checked compiler entries without finite fixture enumeration |
| M5 — Backward campaign resumed | Projection movement and later passes composed through the common interface |
| M6 — Trust/release closure | Alpha bridge removed or explicitly accepted; hosted required gates and protected `main` |
