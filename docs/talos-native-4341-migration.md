# Native Talos 4.34.1 migration

Candidate: upstream Talos `80644390de3ad4db3055445259a034413ae41577`.
Base: accepted FIR `15dc1f46025a498474e39f5660bc82053d588dcf`, followed by
evaluation `03f05a38f1f64616fcf3eaf2cdff547cda722e02`.
Root coordinates the dependency decision; this document records local migration
work, not main acceptance or an upstream stable-release designation.

## Dependency setup

Setup commit `ac09d451d1ea6ec634f6ae22a73a8afbc4b574a2` selects the native
upstream revision, authenticates pristine tracked source, and removes
`talos.patch` and its old-toolchain fixture wiring. The native interpreter
toolchain, lakefile and dependency manifest exactly match the former patched
outputs. Lean stays at `4.34.1`/`5045d0056413266e57c625dcd7c365b10e377c52`;
mathlib stays at `d13f23b723b8a846827a245b89c10fc7d3f11612`. No transitive
manifest revision changes or Blueprint package/path refresh are required.

The worktree-local `.deps/talos-434/project` layout is preserved for Make,
CI, forced trust audits, retained initializer and Blueprint consumers. Source
mirroring still compares inventory and hashes before/after copying. Wrong
revisions, staged/unstaged upstream source changes and compiler mismatches
are rejected; setup does not silently reset an old or dirty dependency tree.
An old scratch checkout must be preserved under an unused backup name before
preparing fresh native state. No worktree, compiler or published artifact is
deleted by this migration.

The separately reviewed `float-normalization.patch` remains necessary to
prepare the accepted original Float proof source, and retains its exact
original/normalized source hashes. It is a local proof normalization, not
an upstream toolchain patch. W6 owns any subsequent proof/hash changes.
The audited `lean433UpstreamBridge` name and the sole accepted 4.34.1 compiler
profile are unchanged.

## Measured trust reduction

After the local-index repair, the clean proof build reached the exact trust
audit. A complete speculative compiled measurement found three differences
among 324 endpoints: `ConcreteExportTerminatesWith.postconditions_overlap`,
`not_trapsWith`, and `uint64_result_unique` each lose only `Classical.choice`.
All other 321 exact inventories match, including recorded generated debt.
Root reviewed and approved precisely those three expectation changes; strict
equality, every other inventory and all negative controls are unchanged.
The endpoint source propositions and premises are unchanged.

Dependency tracing used an isolated accepted-main control at `15dc1f460`,
with its official `0e05edbc` overlay, and the native candidate on the same
Lean/mathlib 4.34.1 identities:

| Compiled dependency | Accepted overlay | Native candidate |
| --- | --- | --- |
| `Wasm.run` | propext, Classical.choice, Quot.sound | propext, Quot.sound |
| `Wasm.f32Add` | propext, Classical.choice, Quot.sound | propext |

The old `Wasm.f32Sqrt` also has the three standard dependencies. Candidate
`Wasm.execOne` and the `ConcreteExportTerminatesWith` definition have exactly
propext and Quot.sound. Thus the reduction reaches these endpoint *types*
through the execution definition as the native Float/model implementation is
replaced by Talos's integer-ratio IEEE754 model; it is not a change to their
local proof statements. No artificial choice dependency, subset allowance,
new axiom or universal old/new semantic equivalence claim is introduced.

## Upstream differential evidence and emitted subset

The exact candidate's [upstream differential run](https://github.com/cajal-technologies/talos/actions/runs/37463783118)
is red because ten documented constant-initializer/element-segment exceptions
became stale. The run reports 566 agreements, 22 rejected/unsupported decode
cases, 27 invalid-module acceptance differences, and five unsupported cases.
The candidate's unchanged `differential/baseline.json` describes those exact
exceptions; the final errors are stale entries, not newly wrong numeric values.
This does not establish completeness or soundness of the general Talos validator.

`FirTalos.Adapter.adapt` first runs `Fir.Wasm.validateModule`, then builds a
Talos module with numeric params/locals/results, ordinary numeric global
values, optional wasm32 memory, functions/imports and function exports.
It does not populate tables, element/data segments, GC type declarations,
exception tags, reference-typed locals, subtype hierarchies or reference calls.
Assessment of the exact baseline against this construction is:

| Baseline family | FIR boundary |
| --- | --- |
| Ten stale const-init/element exceptions | Their table/element/GC initialization shapes are not emitted by the adapter. They remain upstream CI maintenance work. |
| Twenty-two WAT decoding gaps | The reported named data/GC/element/table forms are not produced by adaptation, which builds the AST directly. This does not approve a future arbitrary-WAT import path. |
| Twenty-four reference/GC/subtype/table/exception acceptance differences | Require shapes or instructions outside the adapter's constructed module surface. |
| Three numeric acceptance differences: block-result-type, func-result-arity, func-return-type | Relevant validator limitations. FIR independently checks function fallthrough/return types and arities and block/branch operand stacks before adaptation; do not treat target validation alone as a complete typing theorem. |
| Five unsupported cases | Reference calls/exception instructions or invalid extended float initialization; not the constructed FIR adapter path. |

The numeric boundary assessment is source inspection of
`Fir/Wasm/Validate.lean` and `integration/talos/FirTalos/Adapter.lean`, not a
new universal exclusion theorem. Full source/target proof, trust and engine
gates remain required. No upstream baseline entry is changed or allowlisted
locally to make CI appear green.

Floating arithmetic and conversion instructions are emitted and therefore
remain directly relevant. Upstream now uses an integer-ratio IEEE754 model
instead of opaque native Float operations. Candidate kernel examples exercise
rounding ties, subnormals, overflow, signed zero, NaNs, square root and integer
conversion boundaries; these complement, rather than replace, FIR's resident
Float proof and artifact/source-engine checks. The full validation examples
also exercise the new select/table/local-initialization rules. Both exact
upstream example modules build successfully against the pinned candidate.

## Validation and remaining work

Setup identity/source-mirror negatives, shell syntax, `make talos-setup`,
`make check` and focused Adapter/Execution/ConcreteResidentMemory builds pass
on the native dependency setup checkpoint. Root reassigned the unclaimed W6 and W7 leases exclusively to this lane.
The eight-file proof migration spells out the unchanged bounds
`index < params.length + locals.length` and explicitly supplies setter input
frames, preserving value stacks that can no longer be inferred through the
removed upstream predicate. The checked-local lemma passes a Beam probe and
checkpoint, the explicit big-numeric frames pass Beam diagnostics, and the
clean Float/full proof umbrella plus forced 324-endpoint trust audit pass.
No definition is
restored in Wasm's namespace and no premise or trust obligation is weakened.

The first exhaustive artifact/browser-gate attempt stops in the unchanged
`FirWasmSourceExample.lean` resident Format closure-projection inventory:
104 operations cover eight distinct coordinates, while the twelve-coordinate
ratchet expects object indices 0..4, tobject 0..3, uint8 0..1 and uint32 1.
Actual coordinates are tobject 0..4, uint8 0..1 and uint32 1. Five old object
coordinates are absent and tobject index 4 is new. No incorrect generated
execution is established. An isolated accepted-main control with the old Talos
overlay fails identically with `FIR_PRETTYM_CHECKPOINTS=1`; without that flag the
fixture returns before resident inventory checks. Candidate and control have
identical 104 projection imports, descriptor/dispatch tables and captured LCNF.

The accepted compiler policy `closureProjectionKind`, introduced in
`645907212` (align partial captures with Lean's object ABI), widens object-like
projection *results* to tobject while retaining raw stored descriptor kinds.
`AbiKind.refines` permits exactly this widening. The fixture erroneously
compared normalized runtime results to the raw source-capture catalogue.
Index 4's two projections belong to `prettyFormatRawMonad._lam_9` and `_lam_6`,
both with arity 6 and fixed capture count 5. They correctly return tobject.

The fixture repair canonicalizes and deduplicates every expected raw coordinate
through the existing compiler policy. This keeps all twelve source coordinates
represented by eight result coordinates, the 104-operation accounting,
bidirectional coverage, stable descriptor/dispatch and helper-export checks.
Negative probes reject a same-count wrong index-4 result kind, same-count loss
of index-4 coverage and a dropped operation. The focused checkpoint fixture
passes. No compiler, runtime/helper definition, descriptor layout or ABI is
changed. The tracked card is
`bugs/FIR-BUG-wasm-none-format-closure-coordinate-ratchet.md`.

The companion JavaScript checker derives the exact closure-projection helper
export set from pre-link projection imports, rejecting missing and extra exports.
The focused Lean fixture and complete resident-family JavaScript checker pass.

## Separate host lifetime blocker

The exhaustive artifact gate now reaches the resident-release client and stops
at `ConcreteHost.constructorDescriptor`: the cached descriptor has two fields,
while the reused live constructor header has one field and two scalar bytes.
The full history and minimized public release/allocation helper reproduction
are recorded in `bugs/FIR-BUG-wasm-none-resident-release-host-descriptor-lifetime.md`.
An accepted-main control with only the two validation repairs fails identically.
Candidate and control release Wasm SHA-256 is
`7b3cd8a2f678cd4dedc891d557995b771862aa9909bf31a51f1c7ada4d1ec34b`.
The unchanged host source SHA-256 is
`934b6beb5ae5933a246389a2e55d4f95334ae6525fbbf5b7a6fd86065877ea82`.
This is a pre-existing host metadata lifetime defect, independently of Talos.

Root delegated a separate host repair with unchanged lifetime, ownership and
corruption guards. The additional same-layout diagnostic establishes an exact
interface boundary: legitimate release/reuse from [erased,tobject] to
[object,tobject] and an illicit live erased-slot mutation produce identical
entire physical heaps, frontiers and host provenance maps. Both reject erased
field decoding. Persistent traversal already includes erased slots and marks
the child; no skipped ownership is established by this control. The raw
module-client export contract provides no guest-call notification and the
monotonic frontier does not observe exact-size reuse. A trustworthy lifetime
signal or explicit JavaScript guest-execution metadata epoch contract is needed
before generic reconciliation can also preserve the requested corruption
controls. The provider/ABI decision was returned to root before implementation.
No host guard or emitted code is weakened.

Full artifact failure log SHA-256:
`f94407bdd7eba452e6b03856b0be85c26defea343bcb842345d392abfddf6b36`.
Detailed resident release history log SHA-256:
`116f3ddbfad60c41826e271f4d331ed459dc4ba1e212555596190f51f804a1ab`.
Both captured LCNF inputs SHA-256:
`2a2db2e233c6fa3e94e241016e8e6aaed2f253a919eb56cae48085036fd71ca5`.

## Consumer checkpoint

- Native setup identity negatives, full proof umbrella and forced exact trust
  audit pass; the eight-file proof migration and three reviewed expectation
  reductions are separate commits.
- Retained-initializer checks pass from immutable lean-zip
  `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21` and zip-common
  `4425bab1f9522307d77e8d485bc536149ba31c36`, with worktree-local archives/state.
- Blueprint build and `vbp check` pass (114 manifest/cache entries, no errors).
  No unrelated package pin, path or proof narrative changes are necessary.
- Combined-source `make check` and `git diff --check` pass, including source/engine
  differentials, identity/trust negatives, bug cards and mailbox tests.
- Exhaustive artifact checks pass the repaired inventory and resident-family
  checker, then fail the host descriptor arity invariant. Browser checks are
  not reached. The two tracked diagnostic reproductions preserve all guards.

The local checkpoint is reviewable migration work and a precise shared-contract
blocker; it does not approve the new dependency for main. Completing the host
lifetime repair requires root's boundary decision followed by focused positive
and negative controls and the complete artifact/browser gate. Main landing,
remote publication and destructive cleanup remain separately authorized work.
