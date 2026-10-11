import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Proof policy and contributions" =>
%%%
tag := "contribution-policy"
%%%

This chapter owns the FIR proof-development policy, contribution packet and
statement-revision workflow. Proof work follows the owner assignments in the current checkout, as explained
under {ref "source-disposition-inventory"}[repository protocol]. The historical scalar trust-reduction case supplies an example of
statement, trust and consumer review; its September 2026 scope is not a current
assignment. Publishing an external task follows review of its exact statement
and reproducible environment.

Use the {ref "w6-theorem-menu"}[theorem menu] to identify the promised property
and its current status before choosing an obligation. A proof for a selected
program still covers all of its allowed inputs. Its independent route through
the {ref "w6-proof-mechanism"}[conditional simulation] can guide the general
invariant; future specialization of the general theorem is a later proof route,
not a prerequisite of that initial instance proof.

# Authority, holes and retained conditions
%%%
tag := "contribution-authority"
%%%

The Blueprint is authoritative for its declared target statements and open
obligations. Lean checks statements, proof terms and their composition; FIR's
production contract and trust gates decide acceptance. This selected W6 map
does not claim to cover the entire compiler development. A prose obligation
remains open even when its anticipated dependencies are checked.

Keep statements, assumptions, holes, proof plans, unresolved alternatives and
consumer relationships at their existing Blueprint nodes or chapters, with
supporting source references. A representation difficulty should become a
concrete VBP acceptance case. Ordinary proof advancement remains with FIR's
proof owners; a roadmap's missing mathematics is not an assignment.

Repository setup and integration instructions stay with their operational
owner. Follow the current checkout's ownership, worktree, cache and check
rules, identified under {ref "source-disposition-inventory"}[repository protocol].
The {ref "documentation-migration"}[source-reading account] distinguishes
formal results from their supporting evidence.

The first formal slice in `FirBlueprint/Targets/Admission.lean` separates three
roles:

:::table +header
*
  * Node and declaration
  * Role
  * Remaining review
*
  * {bpref "external-spec"}[]: {name FirBlueprint.Targets.externalSpec}`externalSpec`
  * Explicit definition hole in the existing {name Fir.LeanIR.Impure.ExternalSpec}`ExternalSpec` interface
  * Specify actual primitive request/response behavior and check adequacy and satisfiability for intended implementations.
*
  * {bpref "admission-closure"}[]: {name FirBlueprint.Targets.admission_of_validation}`admission theorem`
  * Direct proof hole constructing the current-step compiler law from the external contract and finite-runtime safety
  * Review the statement and maintained heap-miss/schema-provenance relation before freezing a task.
*
  * {bpref "validated-return"}[]: {name FirBlueprint.Targets.return_of_validation}`return assembly`
  * Checked composition preserving exact observation and result ABI, with admission supplied by the visible hole
  * Recheck consumers when either prerequisite changes; the composition does not establish the draft statements' provability.
:::

The external specification and admission theorem are draft statements under
review. Compilation of their assembly establishes type compatibility; it does
not establish satisfiability, provability or contributor readiness.
Address-space safety, header/capture capacity, cache alignment, parameter arity
and the entry runtime relation remain explicit execution or entry conditions.
Their retention needs mathematical review, with the scope described at
{bpref "address-space"}[], {bpref "finite-runtime"}[] and
{bpref "conditional-return"}[].

Every missing compiler fact needed by a target must stay named and reachable
from its consumer until discharged by a checked proof. Moving a missing fact
into a hypothesis creates a conditional result and leaves its construction
open; the checked assembly must show where that construction is consumed.
An external contract must describe primitive behavior without encoding compiler
admission, choosing future target executions, adding arbitrary caller invariants
or excluding accepted source constructs. Existing trust debt does not authorize
new assumptions or weaker public conclusions.

Planning holes belong in `FirBlueprint/Targets/`, associated with stable nodes
before dependent automatic inference. Preserve those paths when refactoring
helpers. An axiom, unassociated helper, inference exclusion or weakened
conclusion cannot replace an unresolved obligation while certifying the
original goal. Production proof modules must never import Blueprint targets;
FIR's no-placeholder and exact compiled trust gates continue to apply.

# Completion evidence and contribution readiness

Use VBP's built-in status machinery and FIR's existing production evidence.
Do not build a second FIR graph traversal, coverage checker or status database.
The authoring requirement for named obligations is additional to automatic
incompleteness detection: a transitive hole must prevent a completion claim,
and a reader still needs an account of the missing mathematics.

Writing $`\mathcal A(d)` for a declaration's transitive axiom footprint, the
desired completion condition includes

$$`\mathrm{sorryAx}\in\mathcal A(d)\;\Longrightarrow\;
  d\text{ cannot be reported as dependencies-complete}.`

Lean exposes the relevant footprint through {name Lean.collectAxioms}`Lean.collectAxioms`. This is a
required status property, not a law proved by this chapter. BP-FIR-09 reproduced
its violation for an unassociated admitted helper at VBP `19451b0`; the reviewed
experimental PR475 review verified a correction for that case. The current
package retains accepted VBP `19451b009`; named holes and Lean's proof evidence
remain necessary when inspecting its known status limitation.
The separate review of `b2c83f7f`
found lost simultaneous statement/proof-gap evidence. The
{ref "pr475-status-cases"}[completion evidence cases] identify the tested
revisions and reproduction inputs; they do not certify latest upstream behavior.

Statement adequacy, external-contract satisfiability, retained hypotheses and
specification changes require review beyond computed status. Existing production
axioms remain governed by the exact FIR trust inventory. The
{ref "frontier-cases"}[frontier account] explains the distinction between a
local hole and an assembly with incomplete prerequisites.

:::table +header
*
  * Question
  * Evidence needed
*
  * Is a declaration formalized?
  * Its exact checked statement/body and direct or inherited gaps.
*
  * Did a contribution remove a premise or axiom?
  * The affected parent's before/after hypotheses or exact transitive axiom sets.
*
  * Is a task ready for a contributor?
  * A scoped rough-statement refinement goal, or a reviewed fixed statement for proof submission, with environment, owner and permitted scope.
*
  * Is a result accepted by FIR?
  * The exact integrated commit and existing production contract/trust gates.
:::

An open node is not automatically a ready Prove2Me task. A service's acceptance
of a proof is a separate event from FIR consuming it. The existing
{bpref "nat-add-realization"}[], {bpref "nat-add-admission"}[] and
{bpref "nat-add-site"}[] example is distinct from the historical scalar tasks:
its validation-to-call-shape and ABI input construction remains under statement
review. General heap lazy-miss closure and the whole fault counterpart are too
broad for the first external contribution.

# Stable identity and statement revisions
%%%
tag := "statement-revisions"
%%%

A stable Blueprint label identifies a development obligation across revisions.
It does not identify an immutable theorem type or a proof's evidence boundary.
For now, Git provides revision identity. A review or task packet fixes the
label, exact Lean declaration, immutable FIR commit, toolchain and dependency
manifests, intended assumptions/conclusion and affected consumer declarations.
Any service task ID is an external reference to that label; it does not replace
the declaration and reviewed statement as mathematical identity.

If a contributor receives {bpref "admission-closure"}[] and its premises or
internal relation change during proof work, the old proof/task/result remains
evidence about its original revision. A checked proof for the revised statement
does not complete the previous task until the specification change and its
consumers have been reviewed. A change of retained assumptions is material even
when the label and theorem name are unchanged.

Record changed assumptions and conclusion, the reason for the change and its
affected consumers in the functional commit, and update the Blueprint account.
Recheck composition and trust evidence in the pinned environment. Review an
external contribution against the statement revision originally supplied to
the contributor; never silently retarget it or reuse old assembly evidence for
the changed statement. A reviewed replacement may then become the new task
boundary under the same development label.

BP-FIR-10 leaves the VBP design open: separate development identity, statement
revision identity and proof evidence identity, possibly through declaration/type
fingerprints or explicit revisions. A unique node ID alone cannot identify a
changed type. No new fingerprint algorithm, node migration scheme or validation
registry is imposed by this experiment.

A fixed-program instance keeps its statement identity when its proof route
changes. The independent plan for {bpref "stored-export-instance"}[] may later
be replaced by specialization of {bpref "validated-return"}[]. Review that the
same quantified inputs, retained conditions, source runtime/observation and
selected-ABI return property survive. Stronger initializer witnesses and the
source application roundtrip remain separate theorems; the shared compiler
property licenses this proof replacement.

# From a selected obligation to an accepted contribution
%%%
tag := "contribution-packet"
%%%

Select an exact production use and a consequence that can be checked at its
parent theorem. Candidate selection recorded in `ROOT-W6-20260928-100` was
review, not assignment. Its three categories remain useful selection criteria:

:::table +header
*
  * Candidate area
  * Intended consequence
  * Review before assignment
*
  * Non-directional producer/use-site fact
  * Remove a semantic argument or return-provenance input at an admission consumer.
  * Select the exact production use and review its quantified statement.
*
  * Construction-preservation lemma
  * Carry entry cutoff/scope through an intermediate initializer state.
  * Check W6 ownership and the current maintained-invariant design.
*
  * Contained native-axiom reduction
  * Reduce an exact transitive trust inventory with a kernel proof.
  * Review the proof interface and bounded scope; the dated T1/T2 decision below grants no current lease.
:::

A labeled rough statement is already a useful contribution boundary for
statement refinement/formalization. Supply its intended property, retained
conditions, unresolved alternatives, source evidence, current proof route and
consumer. A precise Lean signature can be an outcome of that work. For example,
{bpref "stored-export-instance"}[] fixes the semantic property and universal
input scope while its admission proof is designed. A fixed-statement proof
submission additionally requires the following reproducible packet:

1. Stable Blueprint label and exact intended parent consumer.
2. Exact Lean statement and imports, with a plain-language reading of every
   hypothesis and the conclusion.
3. Immutable FIR commit, Lean toolchain and Talos/Blueprint dependency manifests
   sufficient to reproduce the package environment.
4. Prerequisite declarations, unresolved interface dependencies and a short
   suggested argument; a conjectured interface must be identified as such.
5. Permitted axioms and a focused local check command.
6. Owner/review contact, bounded write scope and integration path.
7. Separate acceptance criteria for the returned proof and for its consumption
   at FIR's parent theorem.

Use FIR's real definitions. An extracted portable mathematical subproblem is
acceptable only with a checked bridge back to its FIR consumer in the acceptance
criteria. Copies of definitions that silently drift cannot substitute for the
pinned package. Reproduction must respect the worktree-local cache and scratch
rules of the current checkout; a failed portable environment setup is an integration
finding, not a reason to replace FIR with unrelated definitions.

Prove2Me delivery is experimental. Before publication, verify that the service
can reproduce the pinned FIR/Talos environment and represent the existing trust
debt. Keep the Blueprint useful locally while that is unresolved. No external
task had been published in this pilot's recorded contribution review.

On return, check the exact type and dependency changes in FIR's environment,
review the mathematical argument and build the focused proof cone. Integration
uses the normal `make check`, worktree-local `make talos-setup` and
`make talos-check` gates. Public contract regressions protect the parent endpoint.
The handoff supplies the proof patch, short mathematical explanation, exact
tested commit, measured axiom/premise changes and the consumer using the result.
FIR's normal owner and integration rules determine landing; a service result
or an editorial Blueprint status does not grant a lease or publication authority.

Measure success at the parent endpoint: did the proof remove a stated premise
or trusted dependency, and what effort was needed to understand, prove and
integrate it? A standalone checked replacement or a deleted inventory string
is insufficient evidence of that consequence.

# Historical scalar trust-reduction case
%%%
tag := "scalar-trust-history"
%%%

The following is the September 28, 2026 scope review of the original T1/T2
packets. Production statements were drafted against FIR
`81bb0e2abfac0270f76844bb5d193dec945844e4`; W6 reviewed the packet at pilot
`e5d56dffdd8c726bb4720abd68ba19bd622f1955` in
`W6-ROOT-20260928-011`. This was a static source review with no production edits
or fresh gates. Both declarations were already proved and usable under FIR's
audited trust policy. The proposal reduced trust; it did not assert that their
behavior was unproved or discharge compiler current-step admission.

The environment was Lean `4.34.0-rc2`
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Talos
`0e05edbcfbb105b33e90c60b4f50e2cf193d9254`, mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, with the official
`tooling/talos-434` manifests and patches at the production commit. The reviewed
Blueprint manifest at the pilot commit pinned VBP
`19451b009e306e7436b82f4d9093c4d15f8cdfd8`. Those immutable Git objects recover
the reviewed environment and the following statement transcriptions.
Historical RC2 evidence does not prescribe a local pin
override for new work; ordinary feature work follows accepted main's toolchain.

## T1: decode the permitted scalar kind

The unchanged declaration is
{name Fir.Wasm.Concrete.scalarFromType_boxedScalarKind}`Fir.Wasm.Concrete.scalarFromType_boxedScalarKind` in
`Fir/Wasm/Concrete/BoxingCorrectness.lean`:

```
theorem scalarFromType_boxedScalarKind (kind : BoxedScalarKind) (payload : UInt64)
    (allowed : kind.allowsTaggedRepresentation = true) :
    scalarFromType kind.semanticType payload =
      .ok (BoxedScalar.ofPayload kind payload).semanticValue
```

For kind $`k`, payload $`p`, semantic type $`\tau(k)`, tagging policy
$`a(k)` and semantic scalar value $`\nu(k,p)`, this says

$$`a(k)=\mathrm{true}\;\Longrightarrow\;
  \operatorname{scalarFromType}(\tau(k),p)=\operatorname{ok}(\nu(k,p)).`

Decoding a permitted tagged scalar at its semantic type therefore agrees with
the concrete payload model. Its consumer is tagged scalar unboxing refinement,
including {name Fir.Wasm.Concrete.LiveHeapRel.readBoxedScalar_tagged_refines}`LiveHeapRel.readBoxedScalar_tagged_refines` in the same namespace.
The reviewed public compiler-export inventory included ten generated axioms
under T1's name. A full replacement's measurable result would remove them at
the actual audited consumers with unchanged type and no new nonstandard axioms.

The UInt8/16/32 branches need fixed type expressions to pass the Boolean tests
in {name Fir.LeanIR.Impure.scalarFromType}`scalarFromType`. At the pinned Lean source, `Lean/Expr.lean:809–812` supplies
`BEq Lean.Expr` through opaque {name Lean.Expr.eqv}`Lean.Expr.eqv`, with external implementation
`lean_expr_eqv`. Unfolding scalar kinds, replacing {tactic}`native_decide` by {tactic}`decide`
or proving structural inequalities does not expose the needed Boolean equations.
W6 found no applicable proof-facing law in the inspected source. Full T1 was
blocked on that interface; no bridge axiom was authorized. A runtime-classifier
change would be a separately reviewed shared semantic contract.

### The smaller, unassigned UInt64 proposal

The tagging policy for {name Fir.Wasm.Concrete.BoxedScalarKind.uint64}`.uint64` reduces to {InlineLean.lean}`false`, contradicting the existing
`allowed` hypothesis. The historical branch nevertheless used four
{tactic}`native_decide` tests. W6 proposed the same elimination pattern already used
for USize/Float32/Float:

```
| uint64 =>
    simp [BoxedScalarKind.allowsTaggedRepresentation] at allowed
```

The source-based expectation was ten generated dependencies becoming six,
with four unreachable-branch assumptions removed at affected consumers.
This was not an exact compiled audit. The proposal was ready to scope in that
dated review but unassigned, with no proof lease. It did not resolve the other
UInt8/16/32 equations or complete full T1.

A future bounded lease would cover only this branch and its exact affected
trust inventory, serialized by W6. Its proposed acceptance was
`lake build Fir.Wasm.Concrete.BoxingCorrectness`, followed by exact theorem and
consumer axiom audits. Review the measured endpoint sets and generated-name
renumbering; do not widen allowlists or call the result standard-axiom-only T1.
The remaining six generated dependencies would retain the existing audited
policy. Any integration would additionally use the normal FIR/Talos gates.

## T2: match the scalar boxing policy

The unchanged simp declaration is
{name Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar}`Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar` in the same module:

```
theorem boxUsesTaggedRepresentation_boxedScalar (scalar : BoxedScalar) :
    boxUsesTaggedRepresentation scalar.kind.semanticType scalar.payload =
      (scalar.kind.allowsTaggedRepresentation &&
        decide (scalar.payload.toNat ≤ maxTaggedPayload))
```

For the kind $`k` and payload $`p` of a boxed scalar, writing $`M` for
{name Fir.LeanIR.Impure.maxTaggedPayload}`maxTaggedPayload`, the policy equation is

$$`\operatorname{boxUsesTaggedRepresentation}(\tau(k),p)=
  a(k)\mathbin{\&\&}\operatorname{decide}(\operatorname{toNat}(p)\le M).`

The source type-specific boxing rule matches the concrete kind policy and
payload bound, including heap-only kinds. Consumers include {name Fir.Wasm.Concrete.semanticBox_split}`semanticBox_split`
and scalar boxing refinement in the same namespace. The reviewed compiler-export
inventory included seven generated axioms under T2's name. Full replacement
would remove them at the audited consumers while preserving simp behavior and
all production definitions.

The {name Fir.Wasm.Concrete.BoxedScalar}`BoxedScalar` projections and policies do not supply equations for the same
opaque expression equality in the source type guard. Full T2 was blocked until
an independently justified proof-facing law or a separately reviewed classifier
change became available. T2 was not a concurrent assigned task with the narrower
T1 proposal, and no bridge axiom was proposed.

## Trust and status consequences

A full replacement packet allowed at most {name propext}`propext`, {name Classical.choice}`Classical.choice` and
{name Quot.sound}`Quot.sound` as transitive proof axioms: no {tactic}`native_decide` escape, new
assumption, altered scalar policy or source exclusion. Importing the old theorem
as the proof of its replacement would preserve the generated dependencies.
Full T1/T2 acceptance remained dormant while the proof interface was missing.
All original hypotheses and the exact conclusion were to be preserved.

This case exposes four separate facts: a formalized usable theorem, an audited
trust footprint, a blocked or unassigned trust-reduction task and the eventual
consumer/integration evidence. Ordinary open/proved status does not express all
four. Neither existing declaration should be labeled mathematically unproved.
The dated counts and expected delta describe the reviewed revisions; they
neither update today's trust inventory nor establish today's task readiness.
