import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "VBP evaluation cases and proposed formalization" =>
%%%
tag := "evaluation-findings"
%%%

Can a reader find useful mathematical work, explain how it advances a selected
compiler theorem, and distinguish a conditional proof from construction of its
assumptions? This chapter contains the acceptance cases, useful reproduction
inputs and design options. Each observation identifies its tested revision;
it is not a fresh test of the latest VBP implementation. Historical review
chronology remains in Git. The source review for this account was on
2026-10-05 at FIR `93c2e7ec7`.

The {ref "heap-miss-evaluation"}[bounded heap-miss pilot] below separately
records actual HTML, CLI and public JavaScript API use on the migrated artifact.

The original baseline used FIR narrative `81bb0e2ab`, VBP
`19451b009e306e7436b82f4d9093c4d15f8cdfd8` and Lean 4.34.0-rc2.
It rendered 24 nodes, 34 edges, eighteen resolving declaration associations
and six open targets. Full/group switching worked without page errors; the
full fit view needed zoom at a 1440-pixel viewport. The first formal slice at
FIR `340f4612a`, Lean 4.34.1 and the same VBP revision had 27 nodes, 41 edges
and twenty-two formal associations. Historical site counts measure neither
theorem progress nor the current site.

# BP-FIR-01: adoption instructions must reach a buildable template
%%%
tag := "bp-fir-01"
%%%

*Observed:* the installed skill recommended `blueprint` from
`leanprover/verso-templates`, but templates main
`15e1532c3ee2c9499474d280f1d6770bc127558c` rejected that name and listed six
other templates. FIR used a checked-in starter.

*Desired:* a creation command documented for a particular release produces a
buildable project; a missing release has a tested, versioned fallback.
*Options:* deliver the named template, pin the creation recipe to its release,
or document a fallback starter. This is an adoption case, separate from proof
correctness.

# BP-FIR-02: defining a premise differs from constructing it
%%%
tag := "bp-fir-02"
%%%

Compare {bpref "admission-interface"}[], {bpref "conditional-return"}[] and
{bpref "admission-closure"}[]. The first defines a law, the second assumes it,
and the third must construct it. Inspect the return theorem's `admission`
binder: definition completeness does not eliminate that assumption.

Ordinary decomposition now exposes {bpref "external-spec"}[] as an unfinished
definition, {bpref "admission-closure"}[] as an admitted theorem, and
{bpref "validated-return"}[] as their checked composition with the conditional
return theorem. Runtime and address-space conditions remain explicit.
The specification and admission statement require mathematical review;
elaboration of an admitted statement establishes neither satisfiability nor
provability.

*Desired:* discover the stronger endpoint, its unfinished specification/proof
ancestors and its retained conditions together. *Options:* use the current
decomposition and prose; defer a special hypothesis-discharge relation until a
concrete case demonstrates a need.

# BP-FIR-03: computed readiness must explain the useful stage
%%%
tag := "bp-fir-03"
%%%

The baseline `query work-queue` included all six open nodes.
{bpref "provenance-closure"}[], {bpref "heap-miss-closure"}[] and
{bpref "fault-closure"}[] had `nextStep: proof` and both axes `ready to formalize`
while lacking Lean associations and carrying review/design notes. The other
three had `nextStep: statement`, proof `not ready`. A rough informal statement
can already support refinement/formalization work; that advice need not promise
a fixed Lean proof assignment. The formal slice recommended proof of admission
while its external specification remained an admitted definition.

*Desired:* explain statement design, exploratory proof, proof under a reviewed
interface, prerequisite work and consumer rechecking. Owner/effort metadata
does not supply an immutable public task. *Options:* an authoring convention,
an explanatory query, or frontier logic using existing axis/origin evidence.
Editorial tags should not silently acquire readiness semantics. The
{ref "frontier-cases"}[selected-goal brief] and its
{ref "frontier-transitions"}[eight cases] specify the explanations to evaluate.

# BP-FIR-04: a graph must expose the evidence behind its edges
%%%
tag := "bp-fir-04"
%%%

`query uses admission-closure` shows an authored plan;
`query uses conditional-return` includes inferred proof/type references through
unassociated helpers. The early overview did not enumerate twenty admission
branches. An empty edge list for a prose target does not establish independence.

*Desired:* preserve statement/proof axes, manual/inferred origin and intent;
identify selected overviews, proposed plans and checked reductions.
*Options:* linked coverage prose, discoverable node evidence, or a decomposition
concept if needed. Axis and origin already survive queries; use
{ref "bp-fir-11"}[BP-FIR-11] to evaluate what additional evidence is required.

# BP-FIR-05: formalization, trust and integration need separate evidence
%%%
tag := "bp-fir-05"
%%%

The conditional return declaration still has the generated axioms listed in
FIR's `TrustInventory`. A locally checked result can also be absent from
accepted main. Completion status alone describes neither condition.

*Desired:* link trust policy/report and exact source, environment and accepted
integration provenance. *Options:* present existing FIR reports with evidence
links; the gates remain their source. The {ref "proof-trust"}[compiled trust
account] explains the boundary. No duplicate validation registry is proposed.

# BP-FIR-06: selected-goal views must retain useful paths
%%%
tag := "bp-fir-06"
%%%

Start at {bpref "closed-export"}[] and identify nearby open obligations and
their reasons; start at {bpref "heap-miss-closure"}[] and identify the consumer
that benefits. Compare full/group views and `query used-by`. Baseline grouping
was useful; the full fit view needed zoom, a measured layout limitation.

*Desired:* collapse completed subarguments while retaining execution conditions,
blocker paths and readable labels. *Options:* existing group/query navigation
and a selected-goal explanation; measure larger maps before replacing the
renderer. The {ref "frontier-cases"}[frontier brief] supplies return-only and
broader export paths.

# BP-FIR-07: discovery must identify the selected Lake project
%%%
tag := "bp-fir-07"
%%%

From FIR root, `lake -d blueprint exe vbp discover` built the right executable
but reported FIR root as `projectRoot` and found no generator. Running
`lake exe vbp discover` from `blueprint/` identified `FirBlueprintMain.lean`
and its chapter. The Make target uses an explicit working directory.

*Desired:* respect the selected project directory or document the caller
contract; failure must be visible rather than an ordinary successful result
with null identity fields. *Options:* project-directory resolution or an
explicit working-directory requirement with a useful diagnostic.

# BP-FIR-08: compact node inspection needs statuses and reasons
%%%
tag := "bp-fir-08"
%%%

At the baseline, `query node conditional-return` exposed associations,
dependencies and previews, but omitted both status fields. Pretty-printed
output was about 102 KB, mainly code/hover data. `work-queue` supplied statuses
only for actionable nodes and could not explain that completed consumer.

*Desired:* compact inspection shares graph status semantics and reasons,
with heavy attachments optional. *Options:* a compact default or a separate
planning query. Compare the conditional theorem with admission without
requiring private graph files.

# BP-FIR-09: a known transitive hole cannot certify completion
%%%
tag := "bp-fir-09"
%%%

At VBP `19451b0`, direct associated holes were incomplete and consumers of
associated holes had incomplete dependencies. A consumer of an *unassociated*
admitted helper was marked `formalizedWithAncestors` with no inferred proof
edges although Lean reported {name sorryAx}`sorryAx`. The minimal reproduction
input in a project importing Verso Blueprint is:

```
lemma helper : True := by sorry
@[blueprint "target" (autoDeps := true)]
theorem target : True := helper
```

*Desired:* Lean's cached transitive footprint prevents completion while
{name sorryAx}`sorryAx` remains; replacing the helper proof by `by trivial` restores it.
Preserve correct direct/associated-hole behavior. *Options:* the narrow cached
footprint correction, with dependency diagnostics as further explanation.
No custom transitive traversal or mandatory generated hole nodes are needed.

The 2026-09-29 maintainer decision removed local `HoleAudit`/`Checks` and their
mutations; checkpoint `ab3e0cbad` retains them. Named obligations and checked
composition remain. The {ref "pr475-status-cases"}[PR475 cases] distinguish the
candidate correction from later classifier/frontier findings. No current
upstream adoption claim is implied by the historical tests.

# BP-FIR-10: stable work identity must retain statement revisions
%%%
tag := "bp-fir-10"
%%%

A contributor receives admission, then its premises or relation change.
The label still identifies the development, while evidence for the old statement
cannot silently certify the new one. Current policy uses a stable label,
Lean declaration, immutable FIR commit, pinned environment and consumer review.

*Desired:* distinguish development, statement-revision and proof-evidence
identities. *Options:* explicit revisions or declaration/type fingerprints for
task export. A unique node ID alone does not identify statement changes;
fingerprint and node-migration designs remain deferred.

# BP-FIR-11: branch coverage must state its reviewed scope
%%%
tag := "bp-fir-11"
%%%

The {ref "admission-coverage"}[coverage chapter] maps all twenty audit rows,
reviewed at FIR `dfa2679f2`. The early overview omitted direct-let, closure-call,
object-field and packed-scalar work. Four explicit prose targets now expose
those families; `schema-admission-bridge` and `lazy-hit-admission` link checked
ingredients. All six were added as authored admission proof prerequisites.
Case admission covers three rows and object-field provenance two; the
{bpref "schema-admission-bridge"}[schema bridge] retains source safety.

*Observed:* edge axis/origin/intent do not alone expose the reviewed inventory,
its scope or remaining preservation. *Desired:* discover the inventory and
revision from admission, every row's destination, unmapped subfamilies and the
distinction between authored coverage and checked assembly. A changed source
constructor triggers coverage review. *Options:* a linked authoring convention,
node evidence links, or a decomposition concept only if needed. No automatic
completeness analysis is selected. Mapped rows, conditional bridges and graph
size do not prove endpoint progress.

# PR475: completion evidence and frontier advice are separate cases
%%%
tag := "pr475-status-cases"
%%%

Initial review tested `558241a3a987e195c0d2312d89b75e05c34250ad` against base
`5d230ee7369bb6c18e667803c75f96dee5377d94`, from FIR
`b23e0779b4086deaf6ee18c84e2bba8853ac891c` on Lean 4.34.1.
Re-review tested `b2c83f7f14d8d247783bd71421b1215ae2ac8916`.
The later mixed-axis report uses that candidate at FIR `4b260be59`.

:::table +header
*
  * Observed case
  * Desired behavior and reviewed disposition
*
  * P1: a structure field depends on an admitted type. Initial candidate saw a sorry footprint but marked the structure complete.
  * Failure to localize a known gap cannot restore completion. Re-review verified the conservative incomplete result; a Nat-field control remained complete.
*
  * P2: validated-return was blocked/incomplete with nextStep proof, despite having a checked assembly body.
  * Preserve local evidence and direct work to prerequisites. Reproduced at re-review; kept as a separate frontier follow-up outside the narrow status correction.
*
  * Combined axes: a statement gap suppressed independently available proof-gap evidence.
  * Preserve both axes before frontier advice. The later report located an array pipeline-scoping error; the earlier no-blocker assessment did not cover this case.
*
  * Hidden imports: a cached sorry footprint may not locate a gap in the visible body.
  * Retain origin and uncertainty or extraction-time evidence. Absence of a direct marker cannot certify local completion.
:::

Keep extraction/classification correction, frontier explanation and imported
body regression coverage distinct. Advice cannot recover discarded evidence.
The candidate's new `SorryInfo.origin` broke decoding of old generated output;
rebuilt output passed. Rebuild artifacts when changing the pin.

The constructor-footprint regression input is:

```
def Gap : Type := by sorry
@[blueprint "record" (autoDeps := true)]
structure Record where
  payload : Gap
```

Known incompleteness must survive even when the structure's own type/body
does not localize the constructor dependency. A completed field-type control
checks that healthy structures remain complete.

The independent-axis regression input is:

```
def Spec : Prop := by sorry
theorem admitted (h : Spec) : True := by sorry
theorem composed (h : Spec) : True := admitted h
```

The admitted theorem needs statement/dependency and proof/direct evidence;
the composition needs statement/dependency and proof/dependency evidence.
The reviewed `b2c83f7f` pipeline lost the latter axis because its second stage
was scoped inside the first conditional's else branch. Treat independent-axis
preservation as a regression requirement, separate from frontier advice.

## Fresh candidate follow-up: local and inherited proof evidence
%%%
tag := "pr475-origin-evaluation"
%%%

On 2026-10-05, a fresh isolated runtime tested PR475 head
`25d9404bc2969da435786c89051d80f03b73ad11`, verified open and unmerged that day.
This is historical candidate evidence. That evaluation's parent artifact used
`b2c83f7f14d8d247783bd71421b1215ae2ac8916`; the current integration package
retains accepted `19451b009e306e7436b82f4d9093c4d15f8cdfd8`.
The consumer base was `daa74e6f29a91e0041d3ec6a8930f5266e652a69`; child commit
`af94eb5276e407eec869ba2c532c9585078abb8e` changed only the Blueprint pin and
manifest. Other package revisions and Lean 4.34.1 were unchanged.
`Targets/Admission.lean` retained SHA256
`acf62af36269f863aa302f8ed683edce59697def5085edf789e12aade853f326`.

The child ran `lake exe vbp build --output _out/pr475-origin`.
Its generated header records that child commit and `2026-10-05T10:41:55Z`;
`vbp check` passed all 111 manifest/cache pairs. The semantic manifest SHA256 is
`8f3aa28894a1030824361d71eba2a1c0d74ab7fb2c2e6f017c94d5addccd8bec`, and the
HTML-cache SHA256 is
`c8ec1f332f96f9e140772183591dfe9913919810cb23229349f2ec7975fd6627`.
Thus this comparison uses newly generated candidate output, rather than
reinterpreting an older artifact or treating checkout metadata as a build receipt.

:::table +header
*
  * Actual association and same-source expectation
  * Fresh CLI and JavaScript data evidence
  * Native declaration badge
*
  * {bpref "admission-closure"}[]: {name FirBlueprint.Targets.admission_of_validation}`admission_of_validation` has a direct `sorry` body; its type also depends on the unfinished {name FirBlueprint.Targets.externalSpec}`externalSpec`.
  * `containsSorry.info` retains both `statement/dependency` and `proof/direct`.
  * contains sorry
*
  * {bpref "validated-return"}[]: {name FirBlueprint.Targets.return_of_validation}`return_of_validation` has a checked exact composition using admission, with no local `sorry`; its type retains the external specification dependency.
  * `containsSorry.info` retains both `statement/dependency` and `proof/dependency`.
  * depends on sorry
:::

Saved `b2c83f7f` pilot exports contained only `statement/dependency` for both
associations. The fresh candidate resolves that tested mixed-axis evidence loss.
Both nodes still report incomplete overall: checked return assembly inherits
the open admission and specification, and retains finite-runtime, address-space,
supported-export, cache/frame and evaluation premises. Neither this successful
extraction nor the checked composition completes the compiler theorem.

The independent native walkthrough used the dedicated candidate preview at
`http://127.0.0.1:8141/`, through a local headless Chrome fallback because the
connected Browser was unavailable. From the known validated-return page it
inspected the declaration badge and statement dependencies, followed the actual
prose link to admission, and inspected admission's badge, dependencies and proof
plan. Both statement popovers exposed {name FirBlueprint.Targets.externalSpec}`externalSpec` as an automatic dependency.
Badge hovers did not print the full two-axis gap list; dependency-origin
`automatic` describes edge extraction, rather than a sorry's direct/dependency
origin. The visible badge contrast and working prose route nevertheless supplied
the requested local-versus-inherited distinction. The generated admission source
link used the exact child commit and lines 23–36, but the actual GitHub click
returned an invalid-ref/404 page because that child ref was unpublished. Local
source inspection supplied the type/body check; remote source publication was
outside this fixture. This was an expert availability check, not fresh discovery.

Nine CLI invocations succeeded: discovery, artifact check, `node`, `uses` and
`used-by` for each label, and `work-queue`. Representative exact commands, from
the child `blueprint` directory, were:

```
.lake/packages/VersoBlueprint/.lake/build/bin/vbp query --site _out/pr475-origin node admission-closure
.lake/packages/VersoBlueprint/.lake/build/bin/vbp query --site _out/pr475-origin node validated-return
.lake/packages/VersoBlueprint/.lake/build/bin/vbp query --site _out/pr475-origin uses validated-return
```

The independently executed public JavaScript modules were
`/-verso-data/api/data.mjs` and `/-verso-data/api/graph.mjs` from that output.
The supported custom filesystem JSON loader exercised `createPreviewData`,
`loadManifest`, `resolveLabel`, `previewKey`, `loadManifestEntry`,
`loadHtmlCacheEntry`, `resolveDeclaration` and `loadGraphs`.
Both declaration records agreed with CLI evidence. The 55-node, 79-edge graph
retained the proof edge from admission to validated return; `uses` exposed the
automatic proof prerequisites separately from statement contracts.
CLI metadata and source/prose hrefs support navigation; CLI node JSON does not
embed the authored informal statement or proof prose.

Admission's separately authored proof facet was available. Return's absent
authored proof facet returned null, as expected: its associated Lean proof and
origin evidence are attached to its statement record. This data/graph probe did
not run JavaScript DOM preview rendering, hydration, math rendering or a separate
Lean authoring API.

Both work-queue rows remained `nextStep: proof`, statement blocked and Lean proof
incomplete. This aggregate advice is sound here and does not promise exclusively
local proof implementation. Retained origin evidence and prerequisite routes
identify the direct admission work and the consumer's inherited gap; no new
queue or status model is required by this result.

The bounded test establishes evidence retention and the native local/inherited
badge distinction for these two FIR associations. It does not establish global
classifier correctness, hidden-import coverage, the P1 structure case or novice
usability. The candidate pin was not integrated into this documentation project,
and no production proof or upstream implementation changed. Raw identity,
CLI/API and rendered receipts are disposable local evidence under
`.deps/blueprint-proof-origin/` in the isolated child and documentation worktrees.

# Proposed upstream formalization roadmap
%%%
tag := "formalization-roadmap"
%%%

This roadmap records upstream laws reviewed on 2026-10-05 and proposed next
proof boundaries. It neither implements a VBP change nor proves these new
status/frontier properties in FIR.

At PR467 head `93efed3b846811099d5bc46b6326632c80d13b94`, the
[contribution laws](https://github.com/leanprover/verso-blueprint/blob/93efed3b846811099d5bc46b6326632c80d13b94/src/VersoBlueprint/Contributions/Laws.lean)
prove collector exactness, permutation/batching equivalence, replay and
collision preservation. Resolver laws characterize successful selection,
associations, support records, priority agreement, complete diagnostics and
congruence for equivalent evidence. The
[production assembly laws](https://github.com/leanprover/verso-blueprint/blob/93efed3b846811099d5bc46b6326632c80d13b94/src/VersoBlueprint/NodeAssembly/Laws.lean)
project accepted priority, exact supports and blueprint-attribute attachment
capability. These laws concern supplied records and successful assembly;
they do not prove completeness of Lean/body extraction or mathematical adequacy
of an associated theorem. The earlier September review used head `fa41e2e`.

Next, express laws for the pure production status classifier, with adapter
regressions connecting actual extracted evidence to those inputs. For a
declaration $`d` and Lean axiom footprint $`A(d)`, the proposed completion law is

$$`\operatorname{Complete}(d)\Longrightarrow\mathrm{sorryAx}\notin A(d).`

The converse is not asserted. The extraction boundary must handle unavailable
bodies and constructor dependencies, preserving uncertainty when a known gap
cannot be localized. For statement/proof gaps $`G_s(d),G_p(d)`, the proposed
evidence-preservation requirement is

$$`G_s(d)\ne\varnothing\land G_p(d)\ne\varnothing
\Longrightarrow\operatorname{Report}_s(d)\ne\varnothing\land\operatorname{Report}_p(d)\ne\varnothing.`

The premise means both gaps are available; it does not assume complete gap
localization for every import. Tests cover direct/associated/unassociated holes,
structures, completed controls, hidden imports and simultaneous axis gaps.

Then specify frontier semantics. A recommendation for work $`w` toward goal
$`g` should supply a justified dependency path

$$`g=n_0\longrightarrow n_1\longrightarrow\cdots\longrightarrow n_k=w,`

retaining each edge's axis, origin and intent and an explanation of the useful
stage. Retained execution conditions remain conditions. Checked compositions
direct work to their prerequisites; prose targets need statement design/review.
Specify cycles, missing nodes, partial authored decompositions and extraction
uncertainty before claiming general frontier laws. Deduplicating work must
retain the distinct reasons it matters to the goal.

Completion soundness, gap preservation and justified frontier paths are
additional proposed boundaries. None of the record/assembly laws establishes
end-to-end theorem adequacy, premise elimination or contributor readiness.
Replay the finite cases at exact candidates and review current authoring/query
surfaces before deciding which upstream changes are needed. The
{ref "external-domains"}[external-contract review] is the statement-design trial;
no external task or proof lease is published by this evaluation.

# Bounded heap-miss pilot: finding work and its consumer
%%%
tag := "heap-miss-evaluation"
%%%

On 2026-10-05, two migration authors exercised the existing site and tools for
{bpref "heap-miss-closure"}[], starting from {bpref "validated-return"}[] and
following its admission argument. This is an authored-expert availability and
interaction trial. The readers already knew the argument and labels; it does
not establish unaided discovery by a new reader, usability timings, or that a
returned proof would satisfy the intended compiler theorem.

## Frozen input and artifact identity

The clean evaluation checkout was FIR
`368eec6f7cc21b1baa3895bffa0c955924e71429`, with Lean
`leanprover/lean4:v4.34.1` and VBP
`b2c83f7f14d8d247783bd71421b1215ae2ac8916`. The CLI reused
`blueprint/_out/migration-complete`; its consistency check passed with 111
paired entries. The generated graph exposed 55 nodes and 79 edges.

The reused site's page header records build revision `93c2e7ec7` and compile
time `2026-10-04T22:48:13Z`. No fresh build at the clean evaluation checkout
was run for these observations. The checkout, preview metadata and generated
build record are different evidence; a preview's `sourceCommit` does not prove
which committed source produced its bytes. The frozen generated-data hashes are:

* Manifest SHA-256: `096bc886b894a4446961ce121e0871d2317ed006199ccaf9eef95e1f4946b4bc`.
* HTML-cache SHA-256: `29981381cb416273352f8a622fc837ff508655fec0ee0d4c2f6900ec15eadab1`.

The HTML and browser API trials used `http://127.0.0.1:8138/`; the file API
trial loaded the frozen artifact through the documented custom JSON loader.
Raw command outputs, API invocations, route snapshots and screenshots remain
disposable receipts under `.deps/evaluation-heap-miss/{cli-api,rendered}/`.
The successor which adds this account has its own source/build identity and
does not replace this frozen evidence or change production proofs or pins.

## Four reader questions and the recovered answers

:::table +header
*
  * Reader question
  * Answer recovered from the exercised surfaces and supporting prose
*
  * What is locally checked, and which premise or restriction remains?
  * {bpref "validated-return"}[] has a checked composition; admission and the external specification remain incomplete. {bpref "construction-entry"}[], {bpref "construction-return"}[] and {bpref "publication"}[] are checked local ingredients, with their actual hypotheses. Construction return retains a fresh-root bound as a hypothesis. {bpref "lazy-miss-boundary"}[] requires an internal supported initializer and excludes object/tobject results; the checked lazy admission consumes that coverage. Entry/runtime, external and finite-resource contracts remain explicit.
*
  * What still prevents general heap-miss admission?
  * Preserve active construction and the accepted saved fresh caller through the general intermediate-state dispatcher, nested calls, return and publication, then derive the central consumer's inputs. The {ref "heap-caller-invariant"}[heap/caller account] distinguishes fresh closed graphs, already persistent results and other ownership-preserving producers. Its smaller maintained relation/result classification remains open; an object ABI does not prove freshness.
*
  * What useful work can start, and is an immutable proof task ready?
  * The stable label and rough informal statement already support a contribution to refine the maintained relation, result alternatives and consumer statement, then propose a formalization. A later fixed-statement Lean proof submission additionally needs its reviewed statement, premises and environment. The accepted fresh caller is already an ingredient in the newer reviewed source; its missing association in this older artifact is an artifact boundary.
*
  * How would this work advance the selected endpoint?
  * The authored route is heap-miss closure to admission construction, then the inferred proof dependency to validated return. Closing this strand contributes to admission; the other admission families and unfinished external specification still remain. Fault closure, resident linking and encoded-artifact correctness are further boundaries, outside this successful-return claim.
:::

These answers combine tool evidence with authored mathematics. A dependency
path explains an intended consumer; it does not prove exhaustive decomposition,
independence of the branches, or that the chosen relation can be preserved.
The miss restriction was visible in rendered prose. Its declaration preview
exposed the signature; a later bounded source check confirmed the quantified
coverage body. That source check is separate from the browser observation.

## HTML, CLI and programmatic API comparison

The actual HTML click route was the home page, Development roadmap, FIR proof
roadmap, validated return, its linked admission theorem, admission's proof
dependency panel, heap-miss closure, its three proof dependencies, then the
construction entry/return/publication ingredients. The route also reached the
heap/caller chapter's accepted successor and publication-policy alternatives,
and followed its lazy-miss restriction link. The local connected Browser
reported no available browser; a separately recorded local headless Chrome/CDP
fallback supplied the 19 route snapshots. The site remained served throughout.

The relevant canonical page routes, relative to the preview root, were:

* `W6___-from-validated-compiler-output-to-execution/Open-proof-frontier/`.
* `W6___-from-validated-compiler-output-to-execution/Constructing-and-publishing-a-fresh-heap-result/`.
* `W6___-from-validated-compiler-output-to-execution/Compiler-derived-facts/`.
* `Heap-construction-and-suspended-callers/From-active-construction-to-restored-caller-code/`.

The CLI trial invoked the already-built project-local executable directly,
from `blueprint/`. Representative exact commands were:

```
VBP=.lake/packages/VersoBlueprint/.lake/build/bin/vbp
$VBP check --site _out/migration-complete
$VBP query --site _out/migration-complete node heap-miss-closure
$VBP query --site _out/migration-complete uses admission-closure
$VBP query --site _out/migration-complete uses heap-miss-closure
$VBP query --site _out/migration-complete used-by heap-miss-closure
$VBP query --site _out/migration-complete uses validated-return
$VBP query --site _out/migration-complete work-queue
```

:::table +header
*
  * Exercised surface
  * Useful result and observed limit
*
  * HTML statements, proof panels and chapter navigation
  * The composition/incomplete-ancestor distinction, authored heap plan, retained miss restriction and open publication alternatives were readable. Complete helper badges did not erase their hypotheses. The statement/code/prose supplied the work and assumptions behind the formalization state.
*
  * CLI `node`, `uses`, `used-by`, `work-queue`, `search`, `code`
  * Dependencies retained statement/proof axis and authored/inferred origin. Reverse queries gave immediate consumers, so the full path required successive queries. `node` supplied metadata, associated Lean code and hrefs but omitted graph status fields and authored heap statement/proof prose; the return record was 98,755 bytes. The queue returned `nextStep: proof` for both the checked return assembly and design-open heap target. `search persistent` returned no block; this selector searches block metadata rather than the full narrative.
*
  * Public JavaScript ESM data/graph/preview modules
  * The `data.mjs`, `graph.mjs` and `preview.mjs` modules under `/-verso-data/api/` loaded successfully. `createPreviewData`, `loadManifest`, `resolveLabel`, `previewKey`, `loadManifestEntry`, `loadHtmlCacheEntry`, `resolveDeclaration` and `loadGraphs` exposed records, code/source metadata, statuses and dependency references. `createPreview` and `renderNode` rendered seven statement nodes and the authored admission/heap proof facets. Browser requests returned HTTP 200 with no page errors; custom preview hydration and math rendering were disabled for this bounded probe.
:::

The API trial actually called the emitted modules; CLI JSON was a separate
surface. No separate Lean authoring/generator API invocation was performed.
Data and graph API versions reported `1`, while the CLI marked its JSON unstable.
The working browser calls used
`createPreview({canonicalBaseUrl})` and
`renderNode(host,{label,facet},{hydrate:false,renderMath:false})`.
The file trial used `createPreviewData({fetchJson})` and
`loadGraphs({fetchJson})` with the supported file JSON loader.

Canonical manifest labels such as `«heap-miss-closure»` resolved; the CLI's
authored spelling `heap-miss-closure` returned `label-entry-missing` through
the API. Unquoted `publication` resolved directly. Reading `loadManifest` and
round-tripping its canonical label worked. The API documentation describes
canonical labels but does not promise CLI alias normalization: this is an
observed contract/usability difference, not an established resolver defect.

Requests for a separate proof facet diagnosed `manifest-entry-missing` for
the Lean-associated helper/return nodes without an authored proof block.
Their statements and associated Lean evidence remained available; this did
not mean the mathematical proof was missing. Likewise `heap-caller-invariant`
is an ordinary Manual section outside the block resolver. Chapter navigation
and existing hrefs supplied prose routes; this trial does not establish a
requirement for every prose section to become a graph node or API block.
`ConcreteStructuredFreshLazyFrame` did not resolve as a declaration in this
artifact, consistently with the chapter's explicit newer-source/older-association
boundary.

## Findings, requests and acceptance

The pilot confirms useful existing capability: the authored argument can be
followed in HTML, immediate dependencies/consumers queried, and actual public
APIs used for status-bearing graph records and rendered block prose. It exercises
{ref "bp-fir-03"}[stage explanation] and reproduces the frozen candidate's
{ref "bp-fir-08"}[compact node inspection] limitation, while exercising the
{ref "bp-fir-02"}[premise/construction] distinction and
{ref "bp-fir-06"}[selected-goal paths]. These are observations at the named
candidate; they do not say whether latest upstream still has those limitations.
No new transitive-hole regression or mathematical adequacy result was tested.

The initial reading of heap readiness was too strict: lack of a reviewed Lean
signature does not prevent useful work on a labeled rough statement. Statement
refinement/formalization is a valid contribution. It is distinct from submitting
a proof of a fixed Lean statement. Local unfinished proof evidence and inherited
incomplete prerequisites remain a separate inspection question; the return's
overall incompleteness is legitimate.

Two workflow goals follow, to evaluate first against existing authoring and API
composition:

* Give selected-goal advice with local-versus-inherited evidence and a justified
  path retaining axis, origin and intent. Acceptance for this case directs work
  to admission prerequisites and heap relation/statement review, preserves the
  object/tobject coverage gap and execution contracts, and does not assign a
  replacement proof of the existing return assembly. An API/CLI consumer can
  locate the rough heap statement and its refinement decisions, while
  distinguishing an unfinished local proof from inherited incomplete
  prerequisites. Existing metadata/tags may suffice; no new task model follows
  from the absence of a fixed Lean statement.
* Provide a tested compact inspection recipe combining status, available
  statement/proof evidence, source/href and supporting-prose navigation.
  Acceptance round-trips the canonical labels across CLI and API, distinguishes
  absent authored proof facets from absent associated proofs, and reaches the
  fresh/persistent/nested-caller alternatives. Document the existing contract
  where it suffices; require a new API feature only for a demonstrated remaining
  workflow gap.

For a fixed-statement proof submission, the
{ref "contribution-packet"}[contribution review] requires a reviewed statement,
pinned environment, retained premises and actual consumer. The label and rough
statement already organize refinement/formalization work. This evaluation
settles no heap invariant.

## Controlled follow-up: a labeled rough statement

On 2026-10-05, one controlled authoring trial tested whether existing labels,
rough statements and editorial metadata suffice to organize the next heap
contribution. The preceding pilot supplied the before receipts; the heap source
was unchanged at clean FIR `4066392438bf82f7d134fac3e540be6dea4fb41f`.
The trial preserved the mathematical claim, label, owner, priority, three proof
dependencies and absence of a Lean attachment. It added the already-used
`statement-review` tag and a paragraph naming statement refinement/formalization,
retained premises and prose routes to the result alternatives and miss boundary.
These tags are editorial metadata, with no proof-completion meaning.

The after trial used the same VBP pin, `_out/rough-statement-trial` and a separate
local preview at `http://127.0.0.1:8139/`. It was a working-tree experiment based
on `4066392438bf82f7d134fac3e540be6dea4fb41f`, with source-diff SHA-256
`584eb71ad1f24e5e42c02de4f54122a9dea5508c6bfebea81a60c02a1c3d62f9`;
the later committed documentation/build is a separate successor.
Raw source, command and API receipts are under `.deps/blueprint-rough-statement/`.
From `blueprint/`, the existing executable was invoked with
`query --site _out/rough-statement-trial` for exactly five selectors:
`node heap-miss-closure`, `search statement-review`, `work-queue`,
`uses heap-miss-closure` and `used-by heap-miss-closure`.

:::table +header
*
  * Surface
  * Before and after observation
*
  * Native heap statement/proof
  * The existing rough claim and plan already organized work. After the edit, the additional tag and explicit refinement contribution were visible; links to the caller account, miss boundary and conditional admission returned HTTP 200. The focused page had no JavaScript page errors or horizontal overflow.
*
  * CLI metadata and dependency queries
  * Tags changed from `open, active-design` to `open, active-design, statement-review`; the after metadata search found the heap node. `node` exposed tags and hrefs, through which its prose was reachable. `nextStep: proof` and both `ready to formalize` axes stayed unchanged. All three manual, regular proof dependencies and the admission consumer remained.
*
  * Public JS data, graph and preview APIs
  * Canonical-label resolution, manifest tag filtering and graph lookup worked. `renderNode` rendered both the revised statement and existing authored proof plan. The graph remained 55 nodes and 79 edges. The preview probe again disabled custom hydration/math rendering; no new reader study or upstream runtime test was performed.
:::

This result supports the existing convention for this bounded workflow. A
labeled rough statement can be assigned for refinement and formalization;
its precise maintained relation and eventual Lean statement can evolve during
that work. CLI metadata/hrefs and JS data/preview composition recover the
supporting prose. Unchanged proof advice is expected, and does not indicate
failure to recognize design work. The trial found no workflow gap requiring
a new readiness enum or task model.

A separate dated source review checked VBP's official default development
branch at `4848fcae2f284427944750ffb2a2309f861410e5`. Its
[Manual](https://github.com/leanprover/verso-blueprint/blob/4848fcae2f284427944750ffb2a2309f861410e5/doc/MANUAL.md)
describes ready-to-formalize/actionable work without a fixed-signature promise;
its [graph logic](https://github.com/leanprover/verso-blueprint/blob/4848fcae2f284427944750ffb2a2309f861410e5/src/VersoBlueprint/Graph.lean#L41)
uses formalization/dependency status rather than editorial tags to choose the
stage. The captured API/CLI references and data runtime matched that trial's pin.
This was source review only: the actual before/after executions remain evidence
for pinned `b2c83f7f14d8d247783bd71421b1215ae2ac8916`.
