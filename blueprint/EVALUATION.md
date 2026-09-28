# Blueprint experiment: dependency graph and proof frontier

## Question and method

Can a contributor identify an obligation that is both mathematically useful
and ready to work on, and explain how solving it changes the public compiler
theorem? The pilot must also help the maintainer distinguish a successful
conditional proof from removal of its assumptions.

Baseline: FIR narrative at `81bb0e2ab`; Verso Blueprint
`19451b009e306e7436b82f4d9093c4d15f8cdfd8`; Lean 4.34.0-rc2. Build the
24-node map with `make blueprint`, inspect the graph and summary, and query
`work-queue`, `uses`, `used-by` and individual nodes. Queries describe the
current generated site, not a persistent task database.

## Baseline outcome

The package builds and renders. Headless Chrome loaded the graph with 24 nodes,
34 edges, full/group views and no JavaScript errors. All 18 declaration
associations resolve. The six open nodes appear in the work queue. Inferred
statement/proof axes and edge origins are retained by the query interface.
The compact group view is useful; the full 24-node fit view needs zoom to read
individual labels comfortably at a 1440-pixel viewport. This is a baseline UX
observation, not a claim that the graph renderer failed.

The pilot also includes [two exact contribution packets](TASKS.md) for removing
native axiom debt from already-proved scalar lemmas. They expose proof-quality
work that ordinary open/proved status does not represent. W6 review and public
contribution-service publication remain separate next steps.

## Findings

### BP-FIR-01: adoption instructions do not reach a template

**Observed.** The installed skill recommends the `blueprint` template from
`leanprover/verso-templates`, but templates main
`15e1532c3ee2c9499474d280f1d6770bc127558c` rejects that name and lists six
other templates. The pilot uses the checked-in Blueprint starter structure.

**Desired acceptance.** The documented creation command produces a buildable
project at the documented version; absent releases have a tested documented
fallback. This is an instruction/template delivery mismatch, not a Lean proof
failure.

### BP-FIR-02: definition completeness does not discharge a premise

**Reproduction.** Compare `admission-interface`, `conditional-return` and
`admission-closure`. The first defines the law, the second assumes it, and the
third must construct it. Inspect the imported return theorem's binder
`admission`.

**Design requirement.** Let the author identify which exact hypothesis an
obligation discharges and which hypotheses are retained contracts. A query
should answer: "Why is this endpoint conditional, and what result removes this
condition?" A definition node marked formalized cannot answer that question.

**Pilot treatment.** Distinct nodes and explicit prose. The link from the
conditional theorem to premise elimination is a `bpref`, because the existing
proof does not depend on the future stronger theorem. Adding a false `uses`
edge would distort both mathematical dependencies and proof status.

### BP-FIR-03: statement readiness differs from contributor readiness

**Reproduction.** Query `work-queue` and inspect `provenance-closure`,
`heap-miss-closure` and `fault-closure`. These are real open obligations, but
some need a reviewed signature and others are part of an active invariant
redesign. Editorial tags do not participate in the computed readiness model.

**Observed query result.** All six open nodes appear in `work-queue`.
`fault-closure`, `heap-miss-closure` and `provenance-closure` have
`nextStep: proof`, with both statuses `ready to formalize`, despite having no
Lean statement and carrying statement-review/active-design tags. The other
three have `nextStep: statement`, with proof status `not ready`. This is a
useful distinction already, but the first three are not contributor-ready.

**Design requirement.** Explain which stage is actionable: statement design,
proof under a stable interface, prerequisite work, or consumer integration.
Readiness should show its reasons and the dependency path to the selected goal.
An owner and effort estimate alone do not establish an immutable public task.

### BP-FIR-04: graph completeness and edge provenance need to be visible

**Reproduction.** Inspect `uses admission-closure` and `uses conditional-return`.
One is a proposed decomposition with selected manual edges; the other derives
edges from existing proof/type references through unassociated helpers.
The admission overview does not enumerate every one of its 20 branches.

**Design requirement.** Preserve statement/proof axes and manual/inferred
origins, and distinguish a proposed proof plan from a checked reduction. Show
whether a view is a selected overview or an exhaustive obligation split.
An empty edge set should not imply independence or proof readiness without
explaining how it was obtained.

### BP-FIR-05: trust and integration are independent evidence dimensions

**Reproduction.** Inspect the `conditional-return` formalization status and
FIR's exact `TrustInventory` entry. Its existing transitive generated axioms
remain debt. A locally checked contribution can also be absent from accepted
main. Neither fact is described by a completed declaration alone.

**Design requirement.** Support linking to a trust policy/report and exact
source/validation provenance, without conflating those with proof completeness.
The existing FIR trust and contract regression gates should remain the source
of this evidence; Blueprint should present it rather than duplicate the gate.

### BP-FIR-06: useful goal-directed views

**Evaluation task.** Starting at `closed-export`, identify its nearest open
obligations and explain why each is open. Then start at `heap-miss-closure` and
identify which consumer would benefit if it were proved. Compare full and
grouped graph views and the `used-by` query.

**Design requirement.** A selected-goal frontier view should collapse completed
subarguments, retain relevant execution contracts, show blocker paths and
preserve readable labels. A contributor should be able to tell whether their
result advances the selected goal. This pilot is small enough for manual
inspection; scaling and layout quality should be measured with larger maps
before proposing a replacement graph implementation.

### BP-FIR-07: nested Lake invocation selects the wrong project

**Observed.** From FIR root, `lake -d blueprint exe vbp discover` builds the
correct executable but reports FIR root as `projectRoot` and cannot find a
generator. Running `lake exe vbp discover` from `blueprint/` identifies
`FirBlueprintMain.lean` and the chapter successfully. The Make target uses an
explicit working directory.

**Desired acceptance.** Either resolve the invocation's Lake project directory
or document this limitation clearly; discovery failure should be immediately
visible to callers rather than looking like an ordinary successful query with
null identity fields.

### BP-FIR-08: node inspection omits the status needed for planning

**Observed.** `query node conditional-return` returns associations, dependencies
and code previews, but no statement/proof status fields. Its pretty-printed
result is about 102 KB, mainly code/hover data. `work-queue` supplies status for
actionable nodes only, so it cannot explain the completed conditional node.

**Desired acceptance.** A compact node-planning query should include the same
status semantics used by the graph, with reasons, and make heavy code/hover
payloads opt-in. A contributor should not need internal graph JSON to compare
an open obligation with its completed conditional consumer.

## Proposed next product work

1. Define the semantics of an obligation that discharges a named premise,
   including multiple consumers and retained contracts.
2. Define an explainable frontier query over a selected goal, separating
   statement design, proof readiness and integration readiness.
3. Add graph views for those semantics and test them on this pilot.
4. Export only reviewed stable tasks to a contribution service, with exact
   statements, dependencies, environment and consumer identity.

These are proposed requirements, not claims that new metadata fields already
exist. Before changing Blueprint, replay the cases above against its current
query/UI behavior and agree which belong in core semantics versus a project
planning layer. No upstream implementation change is part of this FIR pilot.

## Validation of this pilot

- Clean batch `lake build FirBlueprint` and `make blueprint` passed; all 18
  declaration associations resolve. Existing upstream docstring/universe
  warnings are visible; no missing declaration or placeholder is accepted.
- `vbp check` on the persisted site passed with 48 manifest/cache entries and
  zero errors. Chrome rendered 24 nodes/34 edges, switched full/group views,
  and reported no JavaScript errors.
- `make check` passed at functional commit `4617b83ed4637ce9f16e7ca71173a7eb05b92d78`
  after refresh onto `c4b9f3ea0`. This validation paragraph and the board closure
  are documentation-only successors. No production proof or trust inventory
  changed; no fresh full Talos gate is claimed for the documentation successor.
- An incremental Beam importer check encountered a permission error replacing
  a restored `.ilean`; Beam was stopped and the package was cleaned before the
  successful batch check. The first chapter's earlier Beam check was ready
  with zero errors. This build-state incident is separate from Blueprint's
  graph/frontier findings.

The local build remains opt-in (`make blueprint`); the pilot does not yet add a
hosted site or a required Blueprint CI job. Generated outputs and screenshots
are disposable. Reproduction commands and findings above are the enduring
record.
