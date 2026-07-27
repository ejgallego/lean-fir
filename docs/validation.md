# Interpreter validation

FIR validates its executable semantics against Lean programs compiled by the
normal native backend.  The native executable is the source-language oracle;
the first candidate is FIR's interpreter for the final impure LCNF emitted for
the same declarations. A separate direct-LCNF tier compares native Lean
semantics with validation-owned final-impure programs for machine transitions
that the current source compiler does not emit. Direct cases supplement the
source corpus; they are never presented as compiler-output coverage.

```text
Lean source case
  +-- native Lean/C executable -- oracle observation
  +-- LCNF.main -- final impure program -- FIR observation
  +-- LCNF.main -- Wasm compiler -- Node/V8 observation
```

Run the quick corpus with:

```sh
make validate
```

Run the complete native/LCNF/real-V8 corpus triangle with:

```sh
make validate-v8
```

Run the machine-only direct-LCNF corpus with:

```sh
make validate-direct-lcnf
```

Compose and verify all three tiers in one coverage index with:

```sh
make validate-coverage-index
```

Individual cases and tagged groups can be selected directly:

```sh
python3 scripts/validate_interpreters.py --case captured-partial
python3 scripts/validate_interpreters.py --tag quick
```

The backend pair is explicit and defaults to the current validation path:

```sh
python3 scripts/validate_interpreters.py --reference native --candidate lcnf
```

Repeated `--pair REFERENCE:CANDIDATE` options request a directed comparison
matrix and supersede the single `--reference`/`--candidate` pair:

```sh
python3 scripts/validate_interpreters.py \
  --adapter-config configs/v8-validation.json \
  --adapter-config configs/talos-validation.json \
  --pair native:lcnf \
  --pair native:v8 \
  --pair v8:talos
```

The matrix executes and audits each distinct backend exactly once, persists its
result records once, and then compares every requested edge from the cached
protocol results.  Backend execution/domain/audit findings appear in each pair
that uses that backend, while the process exit status counts each backend
finding only once.  Duplicate pairs, self-comparisons, unsafe names, and two
different adapter objects claiming the same name are rejected before execution.
`_build/validation/matrix.json` is the deterministic discovery artifact for the
run: it lists selected cases, participating backends, directed pair-report
paths, de-duplicated global findings, and aggregate backend/pair/comparison
counts.  Automation can start there and open only the detailed pair reports it
needs. Its `inputs` array content-addresses the exact canonical `corpus.json`,
the validation plan when present, and every external provider and adapter
config with SHA-256. Paths inside the checkout use stable root-relative names.
Inputs
outside it use `external/<sha256>/<basename>`, avoiding both machine paths and
same-basename collisions.  The corpus hash is computed from the same canonical
bytes written to disk. Plan, provider, and adapter JSON are read once: those
exact parsed bytes are hashed and retained, closing a parse/provenance race.
Compiler-produced files are kept separately in the matrix's `products` array,
so configuration inputs and executable semantic products cannot be confused.
The matrix also derives two full SHA-256 identities from compact canonical JSON.
`identity.selection` binds the corpus digest and ordered selected case IDs.
`identity.run` binds that selection, participating backends, directed pair
order, every input digest, every sorted backend product, and the exact backend
tool and reported build-input files.  Observations and findings are
deliberately excluded, so repeated
executions of the same evidence contract share an identity even when they
expose nondeterminism or a regression.

Backend tools are distinct from semantic products and do not require product
receipts.  Native validation binds the built `fir-native-oracle` executable and
invokes that captured path directly; it no longer uses `lake exe`, which could
silently rebuild after capture.  LCNF validation binds the resolved Lean
engine, `FirValidationLCNF.lean`, and the consumed
`Fir/Validation/LCNF.olean`, then verifies all captured backend tool files
before and after execution. The direct tier binds separate
`fir-direct-native` and `fir-direct-lcnf` executables, so its oracle and
candidate process evidence remain distinct even though both consume the same
explicit case registry. External adapters likewise bind the exact
PATH-resolved engine and every config-relative runner argument.  The current
LCNF module hash relies on Lean's
embedded import fingerprints for its transitive closure; inventorying every
loaded olean and host dynamic library remains future hardening. The V8 adapter
registers Node and its runner as tools, while the semantic-Wasm provider owns
the compiler-produced `.wasm` and ABI manifests as products.

Every input, backend tool, reported build input, backend product, backend
result/process artifact, and pair comparison is copied into
an append-only content-addressed location beneath `evidence/inputs`,
`evidence/tools`, `evidence/build-inputs`, `evidence/products`,
`evidence/artifacts`, or
`evidence/comparisons`.  Matrix
entries carry the canonical report-relative artifact path and raw-byte SHA-256.
Existing blobs are reused only when their bytes agree; symlinks, non-regular
files, and digest collisions fail closed.  The mutable original config, tool,
product, result, log, or comparison path is therefore not needed to verify the
completed report.  The sorted `artifacts` inventory includes every successfully
parsed per-case backend result, the exact stdout/stderr pair from each current
execution or external build, build-determinism and file-access reports, and
every retained raw file-access trace.  Opt-in build-input replay adds its own
paired process logs, raw trace, sandbox status, emitted input manifest, and
canonical report to the same inventory.  It is assembled from bytes captured
when the files are written, not by scanning a possibly stale output tree.

Verification is read-only and does not execute any backend:

```sh
python3 scripts/validate_interpreters.py \
  --verify-matrix _build/validation/matrix.json
```

Every completed matrix is also retained byte-for-byte under
`evidence/matrices/<matrix-sha256>`.  The harness publishes a strict immutable
manifest at
`evidence/runs/<run-sha256>/<evidence-sha256>.json`, where the evidence identity
hashes the protocol version, semantic run identity, and exact matrix digest.
This one-way wrapper avoids a self-referential matrix hash.  Repeating identical
evidence is idempotent; different observations, logs, comparisons, or findings
for the same semantic contract create distinct manifests in the same run
directory.  A changed input, tool, or product instead changes the run directory.
The mutable `matrix.json` can therefore remain a convenient latest-run discovery
file without destroying previous executions.

An immutable execution can be verified directly, even after `matrix.json` and
all mutable staging files are removed:

```sh
python3 scripts/validate_interpreters.py \
  --verify-evidence \
  _build/validation/evidence/runs/<run>/<evidence>.json
```

The verifier checks the manifest path, identities, retained matrix digest, and
then the complete matrix evidence graph.  The report tree remains relocatable
because all manifest and matrix references are report-relative.

Every matrix also carries a canonical `coverage` object. It reports selected,
present, and successful results per backend; total, unassigned, backend, and
provider findings; comparison and equality
participation per backend and pair; bundle cases, products, and consumers per
provider; and receipt cases, product references, unique products, and optional
execution-access counts per consumer. The immutable evidence manifest repeats
the exact object for discovery without opening the matrix. Both verification
commands print a compact rendering such as:

```text
coverage results: 285/285 successful, 285/285 present, findings 0 (0 unassigned)
coverage pair native -> v8: compared 95/95, equal 95, findings 0
coverage consumer v8 <- lean-wasm-semantic: receipts 95/95, product references 190, unique products 190, opened 190/190 unique products with strace (<N> trace paths)
```

This is evidence-derived coverage, not a trusted counter channel. Offline
verification reconstructs it from retained backend results, comparison
artifacts, findings, provider bundles, product receipts, and execution-access
reports after those underlying objects and raw traces have passed their own
checks. A self-consistently rehashed matrix with an inflated success, equality,
receipt, product, or open count is therefore rejected. The shape is generic:
adding a Talos backend, pair, or provider-consumer assignment automatically adds
the corresponding rows without a Talos-specific reporting path.
The full process-tree trace-path count is operational telemetry and may vary
with the engine or host toolchain; the receipted/opened product counts are the
portable validation claim.

Two immutable executions can be compared after independently verifying both
complete evidence graphs:

```sh
python3 scripts/validate_interpreters.py \
  --compare-evidence <before-evidence.json> <after-evidence.json>

python3 scripts/validate_interpreters.py \
  --compare-evidence <before-evidence.json> <after-evidence.json> --json
```

The human report is concise; `--json` emits the stable versioned comparison
object for CI and downstream analysis. The comparator distinguishes:

- contract drift in selection/backend/pair graphs, retained inputs, products,
  tools, build inputs, provider bundles, and consumer assignments;
- added, removed, and changed semantic outcomes by exact backend/case key;
- portable coverage-claim drift from full operational coverage drift, so a
  changed strace path count is not presented as changed product consumption;
- finding multiset, product-receipt binding, comparison, and exact artifact
  inventory changes; and
- semantic run identity from exact evidence identity.

Changed JSON results contain both retained outcomes rather than only digests.
Inventory changes retain their logical identity and before/after records.
Paths to the two manifests are deliberately absent from the comparison object,
so relocating an evidence tree produces an all-`same` comparison. Differences
are reported data and do not by themselves make the comparison command fail;
failure means that one of the two evidence graphs was structurally invalid.

`make validate` performs this verification immediately after the normal
native–LCNF matrix run. `make validate-direct-lcnf` verifies its direct
native/LCNF matrix, and `make validate-v8` does the same for the three-way
native/LCNF/V8 matrix. `make validate-coverage-index` runs those producers,
then writes and verifies `_build/validation-coverage/index.json`.

The verifier strictly checks schema, names and paths, every retained byte,
ordering and uniqueness, stdout/stderr pairing, summary counts, and both
identities. Retained control-plane inputs are semantic evidence rather than
opaque hashed blobs: the same pure check runs before matrix publication and
during offline verification, strictly reparses every provider and adapter
config, closes provider names/contracts/bundle-manifest paths over the retained
bundles, and closes consumer declarations over the matrix assignments. When a
plan is retained, its ordered pair graph and ordered provider/adapter config
lists must agree with the matrix inputs. Retained plans are parsed lexically;
offline verification never resolves their original config paths against the
current filesystem. Rehashing a self-consistent matrix after changing one of
those declarations therefore still fails verification.
The verifier also reparses retained raw file-access traces when present and
reconstructs their canonical reports. It parses retained backend results,
checks their case/backend
labels, requires both results used by every comparison, and recomputes each
reported equality from those retained observations.  Results and logs remain
outside `identity.run`, so nondeterministic evidence can expose different bytes
without pretending that the semantic input/tool/product contract changed.
Findings or unequal comparisons are valid evidence and do not make structural
verification fail.  `--verify-matrix` and `--verify-evidence` are mutually
exclusive and cannot be combined with run options.  This
stage verifies the complete artifact inventory referenced by the matrix.  The
immutable manifest preserves multiple executions with the same run identity.

CI can check the requested graph into a strict, versioned plan instead of
assembling flags.  `make validate` uses
`validation-plans/native-lcnf.json`, `make validate-direct-lcnf` uses
`validation-plans/direct-lcnf.json`, and `make validate-v8` uses
`validation-plans/native-lcnf-v8-scalars.json`. The latter preserves an
explicit compiler-admission fence while running each of native, LCNF, and V8
once and retaining all three directed consistency edges. A later plan can add
Talos without changing this comparison model:

```json
{
  "version": 2,
  "corpusBackend": "native",
  "providerConfigs": ["../validation-providers/lean-wasm-semantic.json"],
  "adapterConfigs": ["../validation-adapters/v8.json", "../validation-adapters/talos.json"],
  "pairs": [
    {"reference": "native", "candidate": "lcnf"},
    {"reference": "native", "candidate": "v8"},
    {"reference": "lcnf", "candidate": "v8"},
    {"reference": "v8", "candidate": "talos"}
  ]
}
```

Adapter-config paths are resolved relative to the plan file, not the invoking
shell. `corpusBackend` selects the registered backend whose executable owns
manifest discovery and defaults to `native`; the direct plan selects
`direct-native`. Unknown fields, protocol-version drift, duplicate paths or pairs,
self-comparisons, malformed backend names, and an empty graph are rejected.
`--plan` is exclusive with the pair/adapter flags; `--case`, `--tag`,
`--out-dir`, and `--no-build` remain valid runtime controls.

`validation-plans/coverage-index.json` is a second, composition-only plan. Each
tier names one already-produced matrix, selects the directed comparisons that
belong to that tier, and optionally attaches one backend-specific machine
coverage report. The current index keeps three claims separate:

- `source-lcnf` validates compiler-produced final-impure LCNF against native;
- `direct-lcnf-machine` covers explicit machine programs without claiming that
  the source compiler emitted them;
- `wasm-v8` validates the real V8 engine against both native and LCNF results.

Direct cases may additionally opt into native-oracle path attestation without
changing the shared corpus protocol. The recorder compiles the case's named
native helper and explicitly rooted dependencies to final impure LCNF, writes
the formatted dependency closure under
`_build/validation-direct-native-ir/`, and compares `program.lcnf` with the
SHA-256 stored beside that direct case:

```sh
python3 scripts/record_direct_native_ir.py

python3 scripts/record_direct_native_ir.py \
  --case machine-reset-erased-and-repeated-owned-fields --no-build
```

`--record` prints newly observed digests without treating digest drift as
failure. Both modes verify the case's required artifact fragments, so recording
a new hash cannot silently bless an artifact that no longer supports its
semantic claim. Normal mode writes per-case `attestation.json` and aggregate
`attestations.json` evidence, retains the claim and its missing-fragment
diagnostics, and fails when the final-impure artifact changes. Each case has a
canonical `identity.attestation`. The aggregate has distinct
`identity.contract` and `identity.evidence` SHA-256 values: the contract covers
the ordered oracle claims, roots, ownership obligations, and expected compiler
artifact hashes, while the evidence additionally covers the observed
inventories, count results, and direct-path traces. This makes contract drift
distinguishable from a new observation of the same contract.

The aggregate is retained append-only at
`evidence/runs/<contract>/<evidence>.json`. It is relocatable and can be checked
without Lean, the native compiler, or the interpreter:

```sh
python3 scripts/record_direct_native_ir.py \
  --verify-attestations \
  _build/validation-direct-native-ir/evidence/runs/<contract>/<evidence>.json
```

Offline verification checks every per-case identity, sorted unique case set,
the reconstructed contract identity, and the complete evidence identity.
Consumers can therefore accept the contract/evidence pair as a
content-addressed native-oracle product and detect modifications to claims,
normalized ownership evidence, or direct-path evidence without access to the
producer's build tree.

Each attestation also executes the direct native oracle and the explicit LCNF
machine program. Its `directPath` evidence requires equal semantic
observations, the exact case-declared executed form trace, consistent form
counts, a fully classified step trace whose form projection agrees, coverage of
the required administrative transitions, and an interpreter-step count equal
to the retained step trace. The direct `reset`/`reuse` path and the compiler's
lowered `isShared`/`dec`/`oset` path are therefore checked against one semantic
claim without incorrectly requiring their operation inventories to be equal.

The native side additionally derives a versioned `ownershipInventory` from the
formatted LCNF. It normalizes local-name suffixes and records structured
constructor, increment, decrement, projection, projection-decrement,
`isShared`, reuse-write, and declaration operations with canonical fact IDs and
occurrence counts. Case-local `requiredOwnershipFacts` are checked against that
inventory. Inclusive `requiredOwnershipFactCounts` additionally constrain
dynamic occurrences in the retained compiler artifact and record the observed
count for every obligation, including zero; lower- and upper-bound violations
are retained separately. Unknown reference-count attributes fail closed. The
exact artifact hash remains the broad drift detector; normalized facts and
counts now carry all four ownership claims without relying on raw artifact
fragments.

The initial audited set separates four ownership paths: releasing both slots of
a repeated alias from a unique owner, stopping recursive release at a shared
nested child, taking the shared-owner allocation path without releasing its
child, and loading a closed persistent owner graph through
`inc[persistent][ref]` before the shared reset path. This opt-in audit therefore
pins the native compiler path underlying each semantic comparison and can
distinguish resetting the intended owner from an optimizer choosing ordinary
destruction or reusing one of the owner's projected children. Exact count
requirements pin both repeated-alias release slots, every audited reuse write,
the shared-nested increments, and the persistent-owner increments. It is not a
CI tier and does not claim additional native/LCNF/V8 comparisons.

Only the first two tiers attach LCNF machine telemetry. The V8 matrix contains
the source native–LCNF edge for triangular consistency, but the index selects
only its two V8 edges, so neither semantic comparisons nor interpreter form
counts are silently double-counted. A future compiler-produced Wasm plan can
replace or extend the `wasm-engine` tier by configuration; the indexer does not
compile Wasm or impose work on the compiler track.

The indexer structurally verifies every source matrix, checks that selected
pairs and optional coverage case domains agree, and content-addresses the plan,
matrices, and machine reports. Its summary reports both per-tier and unique
case counts, equal semantic comparisons, the union and summed counts of static
and executed LCNF forms, all observed administrative transitions, external
dispatches, interpreter steps, and any obligation or telemetry failures.
`--verify-index` first checks the retained snapshot and then rebuilds the index
from its current inputs. Snapshot checking validates the content identity and
recomputes the aggregate machine coverage, policy evaluation, attribution, and
summary from the retained tier claims. The live-input rebuild remains the
stronger check: it also reopens the plan, matrices, evidence, and machine
telemetry.

The plan's required `policy` turns those observations into monotone regression
checks. Each tier declares minimum case and comparison counts, its required
backend set, and whether it must attach machine telemetry. Aggregate floors pin
unique cases, tier cases, and comparisons. The machine policy pins minimum case
and interpreter-step counts plus required static forms, executed forms,
administrative transitions, and externals. Counts may grow and inventories may
gain members without changing the policy; losing an established floor or
required member produces an explicit deficit or missing-name list. The
evaluated policy and its failure count are covered by the index identity, and
both index creation and verification exit unsuccessfully when the policy is
unsatisfied. This catches removal of a fixture together with its local
obligations, including loss of the direct tier's otherwise source-unreachable
`admin:yield-apply`.

The index's `attribution` block explains where that aggregate coverage comes
from. It records every case, static form, executed form, administrative kind,
and executed external together with the ordered tier list that observed it.
Policy-required items remain in the inventory even when no tier observed them,
so an aggregate failure has a direct uncovered-item witness. Per-tier summaries
also retain contribution counts and the exact items unique to that tier. In the
current baseline, the 97 source cases are shared by the source-LCNF and V8
tiers, the three direct cases are unique to the direct tier, and
`admin:yield-apply` is the direct tier's unique administrative contribution.
The erased-reset fixture also makes `erased`, `reset`, and `reuse`
direct-tier-only static and executed forms. The source tier uniquely
contributes 16 static forms, 16 executed forms, and all nine interpreter
externals. Attribution is derived from the same verified inputs and policy and
is covered by the index identity.

Two retained coverage baselines can be compared without their original build
directories:

```sh
python3 scripts/validation_coverage_index.py \
  --compare-index <before-index.json> <after-index.json>

python3 scripts/validation_coverage_index.py \
  --compare-index <before-index.json> <after-index.json> --json
```

Both inputs pass the relocatable snapshot check before comparison. The stable
comparison contains only content identities, never the supplied filesystem
paths. It reports added, removed, and changed tiers; inventory gains and losses
for cases, static and executed forms, administrative transitions, and
externals; changes in the tiers responsible for an existing observation;
newly covered or uncovered policy requirements; and signed slack changes for
every tier, aggregate, and machine-coverage floor. A regression classification
distinguishes actual coverage or attribution loss, increased policy failures,
and shrinking headroom even while a floor remains satisfied. The command
returns success after two valid snapshots are compared; differences are data
for the caller, matching the immutable-evidence comparator. Use
`--verify-index` when the current source artifacts must also be reverified.

The driver discovers the corpus from the plan-selected manifest backend
(`native` by default), then composes named backend adapters and optional
build-only product providers. Each adapter owns
its execution strategy and optional backend-specific audit; a build may belong
to that adapter or to one shared provider. The shared driver owns protocol
result domains, result artifacts, semantic comparison, and the comparison artifact.
Native therefore remains the default corpus and source-semantics provider without
forcing a future V8 or Talos adapter to imitate native's one-process-per-case
execution strategy.

The implementation preserves that boundary at the module level:

- `scripts/validation_harness.py` owns backend-neutral protocol results,
  observations, findings, artifacts, adapter interfaces, and declarative
  external commands;
- `scripts/validation_lcnf.py` imports the generic layer and owns LCNF execution,
  diagnostics, and form/external coverage policy;
- `scripts/validation_direct_lcnf.py` registers the two direct-case protocol
  executables while reusing the same LCNF manifest and coverage policy;
- `scripts/validation_coverage_index.py` verifies and composes completed
  matrices and optional machine reports into distinct semantic tiers;
- `scripts/validate_interpreters.py` is the thin FIR CLI, native corpus/execution
  adapter, and built-in adapter registry.

The generic module never imports the LCNF module.  A V8 or Talos integration can
therefore reuse it without loading LCNF coverage assumptions.  It also has no
checkout-global root: every command receives the owning build/run context's
explicit root, allowing the same machinery to validate another controlled Lean
project without silently executing in FIR's directory.

Manifest validation follows the same direction.  The generic parser owns the
neutral execution fields and effect-projection shape, canonicalizes them, and
preserves unknown extension keys.  Before selection and artifact writing, each
participating adapter gets one `prepare_manifest` pass.  The LCNF adapter alone
requires and canonicalizes `requiredLcnfForms`, `requiredExecutedLcnfForms`,
`requiredExecutedLcnfFormCounts`, `requiredExecutedLcnfFormTrace`,
`requiredAdministrativeStepKinds`, `requiredExternals`,
`requiredExecutedExternals`, `requiredExecutedExternalCounts`, and
`requiredExecutedExternalTrace`. Count
requirements are nonnegative, unique by form or external name, and may only
strengthen a corresponding static or executed requirement. Each requirement
has an optional inclusive maximum no smaller than its minimum; equal bounds
express an exact count, while `null` remains minimum-only. A zero minimum is
permitted only with a zero maximum: that name must be statically required and
must not be required executed, preventing a misspelled or contradictory
path-exclusion claim. Effect projections retain the independent invariant that
every projected external is both present and executed. Thus a
`native`–`v8` or `v8`–`talos` run does not acquire LCNF obligations merely
because the current native corpus happens to emit them.

An adapter can also be registered without changing the harness.  The config is
JSON, and commands are argv arrays executed directly rather than shell text:

```json
{
  "name": "v8",
  "buildCommand": ["node", "scripts/build-lean-wasm.mjs"],
  "buildReplayCommand": ["node", "scripts/build-lean-wasm.mjs"],
  "buildAttempts": 2,
  "buildFileAccessRecorder": {
    "kind": "file-access-recorder",
    "name": "strace",
    "command": "strace"
  },
  "buildInputReplay": {
    "kind": "build-input-replay-isolator",
    "name": "bwrap",
    "command": "bwrap"
  },
  "runCommand": ["node", "scripts/run-lean-wasm-v8.mjs"],
  "resultDomain": "selected",
  "timeoutSeconds": 120,
  "productManifest": "products.json",
  "buildInputManifest": "build-inputs.json",
  "buildTools": [
    {"kind": "build-launcher", "name": "node", "command": "node"},
    {
      "kind": "build-driver",
      "name": "scripts/build-lean-wasm.mjs",
      "path": "../scripts/build-lean-wasm.mjs"
    }
  ],
  "tools": [
    {"kind": "engine", "name": "node", "command": "node"},
    {
      "kind": "runner",
      "name": "scripts/run-lean-wasm-v8.mjs",
      "path": "../scripts/run-lean-wasm-v8.mjs"
    }
  ]
}
```

```sh
python3 scripts/validate_interpreters.py \
  --adapter-config configs/v8-validation.json \
  --reference native --candidate v8
```

`buildCommand` is optional.  `resultDomain` is `selected` when the command emits
only requested cases and `corpus` when it emits the whole manifest.  Both
commands receive `FIR_VALIDATION_BACKEND`, `FIR_VALIDATION_OUT_DIR`,
`FIR_VALIDATION_PROTOCOL_VERSION`, `FIR_VALIDATION_CORPUS` (the absolute path
of the canonical corpus JSON), and `FIR_VALIDATION_CASES` (a JSON array
preserving the requested order).  Candidate builds therefore happen only
after the native oracle has defined and selected the corpus.  The run command
additionally receives the captured product and execution-tool inventories.
Both phases receive `FIR_VALIDATION_BUILD_TOOLS`, the captured build-tool
inventory; the build can therefore record or check the exact launcher and
driver paths and hashes under which it is running.  The run command writes
protocol JSONL to stdout; stdout, stderr, result records, domain failures, and
comparisons then follow the same path as built-in adapters.

Every JSON external adapter must declare its execution tools in `tools`, and
an adapter with a `buildCommand` must likewise declare `buildTools`.  A tool has a
restricted lowercase `kind`, a normalized report-stable relative POSIX `name`,
and exactly one source locator.  `command` is a bare executable name resolved
through `PATH`; exactly one command tool is required per phase and it must equal
that phase's command at index zero.  A command tool may add a nonempty
`resolveCommand` argv.  The harness runs that resolver in the project root and
requires it to print exactly one absolute path, then captures and binds that
file instead of the direct `PATH` result.  This lets a Lean adapter resolve a
project-selected toolchain executable such as `lake env which lake` without a
machine-specific path or an Elan lookup during sealed replay.  `path` is a
normalized POSIX path resolved
relative to the adapter config, may use leading `..`, and must resolve to
exactly one later argument of the owning phase command under the project root.
Duplicate identities and duplicate sources within a phase are rejected.
`buildFileAccessRecorder` is a separate optional tool declaration with the
reserved kind `file-access-recorder`; its identity and source must also be
distinct from every build and execution tool.  It can record a trace without a
`buildInputManifest`; when both are present the harness additionally enforces
reported-closure coverage.

`buildReplayCommand` and `buildInputReplay` opt an adapter into sealed replay of
its declared build-input closure.  `buildReplayCommand` is a direct argv array,
not shell text.  It may differ from `buildCommand` when the ordinary command is
responsible for dependency scheduling but a replay should invoke only the
compiler action.  Both argv arrays use the same `buildTools` declarations and
are bound to the same captured launcher and path arguments.  The current
`buildInputReplay` contract has exactly `kind`, `name`, and `command` fields;
the kind is reserved as `build-input-replay-isolator`, and the command is a
bare PATH command.  The current implementation is the Linux `bwrap` CLI.
Replay requires `buildCommand`, `buildReplayCommand`, `buildInputManifest`, and
`buildFileAccessRecorder`; a replay argv without an isolator is rejected.  The
isolator is captured, hashed, and retained as a build tool, with an identity
and source distinct from the recorder and all other tools.

`buildAttempts` is an optional positive integer with default `1`.  Values
greater than one require declared products and mean total clean builds, not
retries.  The harness reuses the exact captured argv, environment, corpus, and
selection for every attempt; clears dynamic staging or removes static products
before each one; and compares the complete product inventory plus the
canonical reported build-input closure against attempt one.  It does not
compare compiler stdout or stderr, since diagnostics are not build products.
Those streams are instead retained as paired `build`, `build-2`, and later
attempt logs.

After the final successful attempt, the harness writes and retains a strict
`build-determinism` artifact.  It records every attempt's sorted product and
build-input identities and hashes, recomputes its equality flag during
read-only matrix verification, and requires the final attempt to equal the
products and build inputs used for execution.  A difference becomes a typed
`build-determinism` finding while the final build still runs against the source
oracle, preserving semantic signal alongside the reproducibility failure.
Identical attempts point at the final content-addressed product and build-input
bytes; earlier differing bytes are summarized by digest rather than duplicated
into the successful run's retained product inventory.  `--no-build` performs
no attempts and makes no determinism claim.

Build tools are captured before the build starts; execution tools are captured
after it finishes.  The harness replaces matching argv entries with those exact
captured absolute paths and verifies all captured files after the build and
immediately before and after execution.  Thus a changing `PATH`, launcher
symlink, build driver, engine, or runner alias cannot make either phase execute
bytes different from the recorded tools.  Direct in-process adapter
construction may omit tools for protocol-only tests, but a declarative adapter
cannot.

The run command receives `FIR_VALIDATION_TOOLS`, a compact sorted JSON array of
the captured execution tools.  The matrix additionally includes every captured
build tool.  For both phases it records the backend, kind, logical name, and
SHA-256 while omitting the machine-local path; it retains the exact bytes under
`evidence/tools/<sha256>`, binds their logical identities and hashes into
`identity.run`, and reports the combined `toolCount`.  Tools are provenance,
not compiler products, so they do not use the per-case product-consumption
receipt.  This proves the exact declared launcher/driver and engine/runner
bytes used by the harness.  It does not yet claim a transitive source or import
closure for compilers launched indirectly by those tools.  A `--no-build` run
captures no build tools, so reused products do not falsely claim a build that
the harness did not observe.

An ordinary external build may also emit `buildInputManifest`, a strict
reported-loaded inventory distinct from both tools and products:

```json
{
  "version": 2,
  "scope": "reported-loaded",
  "inputs": [
    {
      "kind": "lean-compiler",
      "name": "bin/lean",
      "path": "/absolute/path/to/lean"
    },
    {
      "kind": "lean-olean",
      "name": "Fir/Wasm/Emit/Source.olean",
      "path": "/absolute/path/to/Fir/Wasm/Emit/Source.olean"
    }
  ]
}
```

The path-bearing build output is deliberately machine-local.  The harness
rejects missing files, duplicate identities or paths, non-absolute paths, and
symlinks in any path component; hashes every declared regular file with
SHA-256; and derives a canonical path-free manifest containing only kind,
logical name, and digest.  The matrix records the canonical manifest and every
member under `buildInputs`, retains exact member bytes under
`evidence/build-inputs/<sha256>`, binds the sorted closure into `identity.run`,
and reports `buildInputCount`.  Read-only verification reparses the retained
canonical manifest and requires exact equality with the matrix closure.

On Linux, an adapter can opt into observational build-closure validation with
`buildFileAccessRecorder`.  The current recorder contract is the strace CLI:
the harness captures and hashes the PATH-resolved recorder as a build tool,
then wraps every build attempt with the captured binary using
`-f -qq --kill-on-exit -s 0 -yy -X raw`, successful-status and no-signal
filtering, and the `open`, `openat`, `openat2`, `execve`, and `execveat` syscall
set.  It records
successful read-capable opens and executable acquisitions, while excluding
write-only and `O_PATH` opens.  Resolved descriptor annotations must produce
absolute normalized paths; incomplete, resumed, relative, or otherwise
ambiguous relevant records fail closed.
The raw output path is randomized and pre-created privately; the harness
requires the same device and inode after strace exits before reading it.

Each successful attempt retains its raw `file-access.strace` plus one canonical
`build-file-access.json` report.  The report binds the captured recorder, raw
trace digest, sorted observed access set, and the machine-local path of each
reported build-input member, with explicit counts and cross-attempt equality
for both the full observed set and reported-input subset.  Full-set drift is
evidence rather than a semantic finding because compiler temporary paths may
legitimately differ; the stricter product and reported-input determinism checks
remain authoritative.  Every path-bearing member of
`buildInputManifest` must occur in the observed set on every attempt.  The
read-only verifier reparses each retained raw trace, reconstructs the canonical
access set, checks the recorder against the retained tool inventory, and
requires the reported-input inventory to equal that attempt's build-input
closure.  Repeat-build, process-log, trace, and report attempt numbers must
agree exactly.  `--no-build` captures neither a recorder nor traces and makes
no access claim.

This evidence says that the traced build acquired a path through a
read-capable open or execution.  It can overapproximate actual consumption and
does not prove that the bytes later hashed by the harness were the exact bytes
seen at open time.  Inherited descriptors, untraced acquisition mechanisms,
and a path swap between acquisition and hashing remain outside the source-build
claim.  An adapter without `buildInputReplay` makes only this observational
claim.

After the final successful traced attempt, an adapter with `buildInputReplay`
runs one separately declared replay build.  Every reported build-input member
and ordinary build tool must have been observed in the final source trace.  The
harness rechecks each captured source file, creates a Linux `memfd` from its
content-addressed bytes, sets mode `0444` or `0555` according to the observed
access, and applies write, grow, shrink, and further-sealing seals.  It then
uses `bwrap --ro-bind-data` with explicit permissions to copy those sealed
source bytes into a new read-only overlay at the original absolute path.  The
payload-visible modification time is bubblewrap metadata and is not part of
the claim.  The canonical corpus receives the same treatment at its protocol
path.  Bindings record the logical identity, SHA-256, target path, access modes,
and corresponding immutable evidence blob
under `evidence/build-inputs`, `evidence/tools`, or `evidence/inputs`.

The current sandbox profile starts a new session, unshares every namespace,
disables nested user namespaces, drops all capabilities, fixes the hostname,
and leaves the network namespace unconnected.  It clears the inherited
environment and supplies only `HOME=/tmp/home`, `LANG` and `LC_ALL` as
`C.UTF-8`, a reconstructed `PATH`, `TERM=dumb`, `TMPDIR=/tmp`, and the exact
`FIR_VALIDATION_*` protocol variables.  `/proc` and `/dev` are recreated,
`/tmp` and its home are fresh, the original project directory is the working
directory, and only the backend's separate replay output directory is writable.
This keeps replay products out of the ordinary product staging directory.  The
ordinary products remain readable through the ambient root, however; any such
read is traced and counted as ambient rather than treated as a sealed binding.
Because the current profile replaces `/tmp` before installing bindings, the
validation output directory (and therefore the canonical corpus path) must not
itself resolve beneath `/tmp`.

The recorder wraps the isolator as well as its payload.  A successful replay
retains paired stdout and stderr, the raw strace file, bwrap's JSON namespace
and zero-exit status, the replay-emitted build-input manifest, and a canonical
`build-input-replay.json` report.  The report contains the declarative argv,
fixed environment, sandbox policy, sealed bindings, complete observed access
set, ambient-access count, reported inputs, replay products, and replay build
inputs.  Product or build-input differences from the final ordinary build are
typed `build-input-replay` findings; equality establishes that the separately
replayed build produced the exact product and reported-closure bytes later used
by validation.

Read-only matrix verification does not rerun bwrap.  It verifies the retained
isolator and recorder identities, reparses the source and replay traces and the
sandbox status, reconstructs every expected binding from the retained
content-addressed inventories, checks the argv, environment, PATH, policy, and
source-attempt number, reparses the replay build-input manifest, checks that
every sealed build-input and ordinary build-tool path was observed with its
recorded access modes, and recomputes the product and closure equality flags.
The sole path normalization is Linux's exact ` (deleted)` procfs suffix when
stripping it yields the already expected binding for that same logical input;
the raw manifest remains retained unchanged.
Trace, status, manifest, report, and process-log inventories must agree
exactly.  `--no-build` performs no replay and makes no replay claim.

This is a sealed replay of the declared closure, not yet a hermetic build-root
claim.  The current bwrap tier mounts the ambient host `/` read-only before
installing sealed overlays.  The dynamic loader, shared libraries, indirectly
launched runtime tools, package-manager metadata, and any other undeclared
readable files may therefore still come from that ambient root.  Their
successful opens and executions contribute to `ambientAccessCount`, but they
are not content-addressed bindings.  The trace also retains the recorder's
limits around inherited descriptors and untraced acquisition mechanisms.
Consequently the strong claim is that the declared inputs, declared build
tools, and corpus were replayed from the exact captured immutable bytes and
produced equal outputs; it is not that every byte consumed by the process came
from the evidence store, nor that the replay is portable to a different host.
A future synthetic-root tier can remove the ambient root once the namespace
shape, symlink aliases, dynamic loader, shared-library closure, and indirect
runtime tools are explicitly inventoried.

`FirValidationWasm.lean` obtains this inventory from the same running Lean
process that emits the Wasm: `IO.appPath` reports the compiler executable,
`Environment.header.moduleNames` reports all direct and transitive imported
modules, and `Lean.findOLean` resolves the artifact loaded for each module.  On
the current toolchain this is materially stronger than `lean --deps`, which
reports only direct dependencies, and than Lake trace hashes, which are not
cryptographic evidence identities.  The reported-loaded scope is intentionally
honest: without the optional strace recorder it does not independently observe
arbitrary IO performed by command elaborators or the host dynamic loader.  With
the recorder it gains process-level path-acquisition evidence, but a file could
still be swapped between acquisition and later hashing in the ordinary build.
With `buildInputReplay`, the reported Lean compiler and olean members are
subsequently supplied to a separate build as sealed, content-addressed
overlays.  The ambient-root limitations above still apply to the compiler's
indirect runtime closure.

The build-input inventory is not copied into process environment variables;
large Lean closures can exceed operating-system argv/environment limits.  It
is an evidence channel.  `--no-build` ignores stale inventories and records
zero build inputs, so reused products never claim a producer closure the
harness did not observe.

The optional static `products` array or dynamic `productManifest` declares
regular build outputs whose bytes affect the backend's semantics.  A dynamic
manifest is a strict `{"version":2,"products":[...]}` object emitted by the
current build; the harness retains it as a `product-manifest` product and
verifies that its declarations exactly match the matrix products for that
backend.  Each declaration has a restricted lowercase `kind` and a normalized
relative POSIX `path` beneath that backend's `FIR_VALIDATION_OUT_DIR`; absolute
paths, traversal, duplicate paths, manifest self-reference, directories, and
symlinks are rejected.  The static and dynamic forms are mutually exclusive
and require `buildCommand`.

The per-backend output directory is disposable staging owned exclusively by
the adapter.  Before an ordinary dynamic build the harness rejects a symlink or
non-directory root and clears that staging tree, preventing a new inventory
from claiming an undeclared stale output.  It then parses and hashes the exact
newly produced bytes after the build.  Static builds remove their declared
stale files before running.
`--no-build` instead captures the existing declared files for deliberate reuse.
Before starting the engine and again after it exits, the harness verifies that
every product still has the captured digest.  Missing or mutated products are
structural validation errors rather than semantic mismatches.

The run command receives `FIR_VALIDATION_PRODUCTS`, a compact JSON array with
each verified product's backend, kind, stable output-relative name, SHA-256,
and absolute local path.  `matrix.json` records the same entries without the
machine-local path under `products`, sorted deterministically and counted as
`productCount`. The semantic-Wasm provider owns the compiler-produced `.wasm`
bytes and manifests; the V8 adapter executes the exact provider bundle selected
for each case. This handoff does not assume one module per case, so later module
sharing does not require another adapter contract.

Handoff is not, by itself, consumption evidence. When an adapter owns products,
each protocol result from the external engine must include exactly one
`validation-products` diagnostic.  Its string value is a JSON array of the
products that case actually loaded, with `kind`, stable `name`, and the SHA-256
recomputed from the loaded bytes.  Every returned result must report a nonempty
subset of the declared products.  This permits a selected case to load only its
own module without falsely claiming the other retained corpus products.
Missing, empty, malformed, duplicate, or undeclared receipts become structured
`audit` findings. Provider consumers instead use the exact bundle receipt
described below; current V8 evidence therefore distinguishes “the provider
produced this module” from “V8 reports consuming this case's exact binding.”

## Shared compiler products

The generic harness has an opt-in provider/consumer path for running more than
one engine against exactly one compiler output. The checked V8 plans use this
path: `lean-wasm-semantic` owns the build once and `v8` consumes its verified
bundle. This separation changes no compiler, semantic-host, Talos, or runtime
behavior and leaves a second engine free to consume the same bytes later.

A provider is a build-only component. Its strict config declares an opaque
four-field product contract and reuses the same tool capture, repeated-build,
reported-input, strace, and sealed-replay machinery as an external adapter:

```json
{
  "version": 2,
  "name": "example-wasm-provider",
  "contract": {
    "format": "wasm",
    "target": "wasm32",
    "runtimeFlavor": "example-runtime",
    "abi": "example-abi"
  },
  "buildCommand": ["lean", "--run", "ExampleWasmProvider.lean"],
  "bundleManifest": "bundle.json",
  "buildTools": [
    {"kind": "compiler", "name": "lean", "command": "lean"}
  ]
}
```

The example values above are illustrative. FIR's checked, plan-referenced
provider config selects the current semantic-host contract as
`wasm` / `wasm32` / `fir-semantic-runtime-v1` /
`fir-semantic-abi-v1`. `FirValidationWasm.lean` emits that contract together
with a sorted product inventory and exact sorted per-case bindings. The V8
consumer checks the provider, contract, complete exposed inventory, bundle
identity, and exact case bindings without reading the provider's private bundle
manifest or assuming case-derived filenames. These identifiers describe the
frozen semantic runtime used for native-oracle
validation; they deliberately do not claim the future concrete Talos
`wasm32-lean64` runtime. Changing either real contract remains a shared-contract
change that must land separately before compiler or engine wiring depends on
it.

The build emits one sorted bundle manifest. Product paths are relative to the
provider output directory, each selected case has an exact nonempty binding,
and products may be shared by many cases:

```json
{
  "version": 2,
  "contract": {
    "format": "wasm",
    "target": "wasm32",
    "runtimeFlavor": "example-runtime",
    "abi": "example-abi"
  },
  "products": [
    {"kind": "wasm-module", "path": "modules/example.wasm"}
  ],
  "cases": [
    {
      "caseId": "lit-nat",
      "products": [
        {"kind": "wasm-module", "path": "modules/example.wasm"}
      ]
    }
  ]
}
```

The harness hashes the emitted files and derives `bundleSha256` from the
provider name, product contract, complete hashed inventory, and case bindings.
It rejects missing or extra cases, duplicate or unsorted declarations,
undeclared references, unreferenced products, owner drift, contract drift, and
identity drift. The bundle manifest is retained alongside its products, while
the logical bundle inventory excludes that metadata file.

An engine adapter consumes one provider and cannot also declare an
adapter-owned build or products:

```json
{
  "name": "example-v8-engine",
  "runCommand": ["node", "scripts/run-example-v8.mjs"],
  "resultDomain": "selected",
  "executionFileAccessRecorder": {
    "kind": "execution-file-access-recorder",
    "name": "strace",
    "command": "strace"
  },
  "productProvider": {
    "name": "example-wasm-provider",
    "contract": {
      "format": "wasm",
      "target": "wasm32",
      "runtimeFlavor": "example-runtime",
      "abi": "example-abi"
    }
  },
  "tools": [
    {"kind": "engine", "name": "node", "command": "node"},
    {
      "kind": "runner",
      "name": "scripts/run-example-v8.mjs",
      "path": "../scripts/run-example-v8.mjs"
    }
  ]
}
```

Every consumer receives the whole verified inventory through
`FIR_VALIDATION_PRODUCTS` and the contract, bundle identity, and exact case
bindings through `FIR_VALIDATION_PRODUCT_BUNDLE`. Before and after each engine
execution, the harness rehashes every exposed bundle product. The private
provider manifest is retained and re-parsed when the evidence is published.
The consumer returns one `validation-product-bundle` diagnostic per result. Its
JSON value names the provider, `bundleSha256`, and the exact
`kind`/`name`/`sha256` products bound to that case. A valid but wrong case's
module is rejected, not accepted as a declared subset. Unlike the legacy
adapter-owned subset receipt, a missing, malformed, or inexact shared-bundle
receipt is a structural validation error, so no unverifiable matrix is written.

A provider consumer may add `executionFileAccessRecorder`. The field is strict,
uses the reserved `execution-file-access-recorder` kind, requires a bare PATH
command whose value equals the recorder name, and is currently valid only with
`productProvider`. Equating name and command binds the retained tool identity to
the command declared by the retained config. The harness hashes the resolved
recorder as a separate backend tool but does not expose it through
`FIR_VALIDATION_TOOLS`. It wraps the bound engine command with the same strict
strace syscall/status filters used for builds and retains
`<backend>/execute/file-access.strace` plus
`<backend>/execution-file-access.json`.

After parsing successful results, the harness takes the union of exact products
named by their provider receipts and requires a successful read-capable open of
every corresponding provider path in the traced process tree. The report binds
the recorder, provider, bundle and trace identities, receipt count, full-trace
access count, and sorted receipted-product access modes. Offline verification
reparses the raw trace, reconstructs the product union from retained results,
and rechecks the retained adapter declaration, recorder tool, path suffixes,
counts, ordering, and opens. Current V8 validation opts into this evidence.
This establishes that the traced engine/runner process tree opened every exact
receipted product. It does not distinguish an open by V8 from one by its runner,
nor attribute a batched process-tree open to one individual case.

Plans opt in by adding `providerConfigs`; one configured provider is built once
even when several engines consume it:

```json
{
  "version": 2,
  "providerConfigs": ["../validation-providers/example-wasm.json"],
  "adapterConfigs": [
    "../validation-adapters/example-v8.json",
    "../validation-adapters/example-talos.json"
  ],
  "pairs": [
    {"reference": "example-v8-engine", "candidate": "example-talos-engine"}
  ]
}
```

Provider and backend names are disjoint, unused or missing providers fail
closed, and each backend currently consumes at most one provider. Provider
products, tools, inputs, and build artifacts occur once in the evidence
inventory rather than once per engine. Opted-in matrices add sorted
`providers`, `productBundles`, `productConsumers`, and exact sorted
`productReceipts` records and bind the bundles, assignments, and receipts into
`identity.run`. Offline verification
rehashes every retained product, reconstructs the bundle from both matrix and
manifest data, and checks each retained result receipt against its exact case
binding. The provider staging directory is therefore unnecessary for offline
verification.

The checked production plans now build the Lean-Wasm provider once and attach
the real V8 consumer. A Talos runner can subsequently consume that unchanged
semantic bundle as a second engine, or declare a distinct concrete-runtime
contract when validating Talos's own interpreter. Talos-owned runner wiring
remains in the Wasm lane; the generic layer embeds neither Talos nor concrete
runtime details.

## Case and observation contract

`Fir.Validation.Corpus` defines each case once.  A case names its source entry,
additional source helpers that must be compiled into the same impure program,
typed arguments and result schema, native invocation, fuel, tags, the LCNF
forms it intends to exercise, and the external names that must be present or
called.  Required-form and required-external checks prevent optimization,
dependency-closure, or compiler drift from silently turning a targeted case
into a weaker test.

Backends exchange versioned JSONL records from `Fir.Validation.Protocol`.
The semantic observation contains termination, stdout, stderr, and controlled
effect events.  Backend failures such as unsupported input, timeout, crash,
malformed output, and fuel exhaustion remain distinct from source behavior.
Result schemas are explicit because final impure LCNF represents `Nat`, `Bool`,
`Unit`, and nullary constructors with otherwise ambiguous tagged values.

The LCNF candidate asks Lean's own dependency collector for the declarations
reachable from the case's compilation roots.  Imported extern signatures are
retained instead of being fabricated, then dispatched through an explicit
reject-by-default validation allowlist.  Structured arguments are encoded into
an initial FIR heap; returned values are decoded using the declared result
schema.

Artifacts are written under `_build/validation/`.  Each case retains protocol
results, backend logs, generated impure LCNF, declaration names, instruction
forms, and the comparison summary.  Process logging, per-case result writing,
result-domain checks, and semantic comparison use actual backend names rather
than assuming LCNF.  Pair-scoped files under
`_build/validation/comparisons/`—for example `native--lcnf.json`—identify their
reference and candidate explicitly.  This is the backend-neutral artifact
boundary used by later V8 and Talos adapters, and it lets native–LCNF,
native–V8, and V8–Talos evidence coexist in one output tree.  Backend names are
validated before being used as path components.  A comparison file is written
for successful and failed comparisons, with selected/compared/equal/finding
counts and typed findings for
`build-determinism`, `execution`, `result-domain`, `audit`, and `comparison`
phases.  Each finding
retains its backend and case ID when applicable, so automation does not need to
recover structure from stderr text.  The native oracle's `--manifest` JSONL is
the single discovery surface for the harness: case and tag selection no longer
depend on a second ad-hoc listing command.  The harness validates and
canonicalizes those descriptors into `_build/validation/corpus.json`, ordered
by case ID with deterministic tag and required-form lists.  Each attempted
comparison embeds the corresponding descriptor, so entry name, provenance,
arguments, schemas, fuel, tags, and intended LCNF/external coverage remain
attached to later differential runs, including semantic mismatches.
`requiredExecutedLcnfFormTrace` is either `null` or an exact ordered form
sequence. A non-null sequence must contain every dynamically required form and
its multiplicities must satisfy the declared form-count bounds; it is retained
verbatim rather than canonicalized as a set.
`requiredAdministrativeStepKinds` is a sorted, duplicate-free subset of the
recognized administrative interpreter transitions. Each listed kind must
occur in that case's `executed-step-trace`.
`requiredExternals` records names that
must occur in the compiled artifact; `requiredExecutedExternals` records the
stronger path obligation that the interpreter must actually dispatch them.
Both fields are required, even when empty, and are canonicalized as sorted
sets. `requiredExecutedExternalTrace` is either `null` (no exact-order
obligation) or an ordered array, where `[]` deliberately requires zero
dispatches. Trace names must exactly reproduce `requiredExecutedExternals`, and
the trace multiplicities must satisfy the declared external-count bounds.
Unlike set-valued fields, this array is never sorted or deduplicated. Each case
also carries an `effectProjections` array describing which
external events become semantic effects, with external name, stable operation
name, argument schemas, and optional result schema.  The field is required and
canonicalized even when empty.  A projected external must also be required both
statically and dynamically.  Future backends can therefore consume the same
effect ABI without importing FIR's Lean definitions.  This manifest is the
backend-neutral input boundary for future adapters, including a real Wasm
engine once the compiler track can provide modules.

`_build/validation/lcnf/coverage.json` is the deterministic aggregate coverage
report for the selected cases.  It keeps two kinds of evidence separate:

- **static coverage** is the set of forms present in each compiler-produced
  LCNF artifact (`lcnf-forms`), checked against `requiredLcnfForms`;
- **executed coverage** is the set of forms the interpreter actually reached
  (`executed-lcnf-forms`), checked against `requiredExecutedLcnfForms`.

Set membership cannot distinguish one write from a sequence of writes. The
runner therefore also emits `executed-lcnf-form-counts` as a JSON array of
positive `{form, count}` records and `executed-lcnf-form-trace` as one ordered
form name per executable interpreter transition. The harness requires all three
views for every LCNF result: trace names must reproduce
`executed-lcnf-forms`, and trace multiplicities must reproduce
`executed-lcnf-form-counts`.
`executed-step-trace` closes the remaining accounting gap. It contains exactly
one item per interpreter transition: either `form:<name>` or an administrative
kind for named/value invocation and yielded bind/apply/cache/final-result
control. Coverage rejects unknown kinds, requires the trace length to equal
`interpreter-steps`, and requires its ordered `form:` projection to reproduce
`executed-lcnf-form-trace`. Executed forms must also be present in the compiled
artifact's `lcnf-forms` inventory. Per-case
`requiredAdministrativeStepKinds` obligations turn selected administrative
transitions into regression checks; the aggregate report retains their union,
missing count, and every recognized kind not observed by the selected corpus.
The source-corpus guards currently require all five administrative kinds emitted
by source-generated LCNF: named and value invocation plus yielded bind, cache,
and final-result control. `admin:yield-apply` remains recognized and reported,
but is not claimed as source coverage: current compiler output normalizes the
curried and function-valued-declaration probes into arity-respecting calls, so
neither reaches the machine's over-application frame. Two direct cases pin both
routes into that apply frame.
`machine-yield-apply` invokes a one-parameter declaration by name with two
values, then applies the extra value to the returned closure.
`machine-closure-yield-apply` first constructs a closure for that declaration,
then performs the same over-application through `.fvar` and
`admin:invoke-value`. Their 14- and 15-step traces each contain exactly one
`admin:yield-apply`; both results, exact form traces, and per-form
multiplicities are compared with the corresponding native curried Lean
application.
The manifest's optional
`requiredExecutedLcnfFormCounts` records `{form, minimum, maximum}`
obligations. The harness requires count telemetry for every LCNF result,
validates it independently, checks that its keys exactly match
`executed-lcnf-forms`, and reports counts below or above their inclusive
bounds. Corpus-wide summaries retain summed observations, required minima, and
bounded maxima. Per-case `requiredObservations` materializes every obligation's
observed count, including zero even though the positive-only runtime telemetry
correctly omits absent forms.

When `requiredExecutedLcnfFormTrace` is non-null, the observed trace must also
match element for element. The initial 18 contracts cover compact control-flow
signatures: Boolean and list branches, recursive and local-tail traversal,
scalar and signed classification, taken/skipped external branches, and
unique/shared constructor reuse. Longer mixed-layout traces continue to
produce consistency-checked telemetry without yet becoming exact obligations.

The `path-exclusion` tag groups fixtures that pin negative control-flow
evidence. Five shared copy-on-write fixtures statically retain `oset` because
the compiled update machinery contains the unique-object branch, but require an
exact executed count of zero. The two multi-object projections, aliased-child
replacement, shared self-replacement, and distinct-child swap must therefore
take the allocation/copy path without silently performing an in-place object
write.

Four branch-signature fixtures pair exact-zero obligations with exact positive
counts. Empty recursion executes one `cases` and one `fap` but no `oproj`.
Same-size unique reuse executes one `isShared`, `setTag`, and `oset`, while
executing neither `del` nor `ctor`. Both grow/delete variants execute one
`isShared` and one `del` while excluding `setTag` and `oset`; the unique result
executes one `ctor`, and the shared wrapper executes two because it also
constructs the returned pair.

External path exclusion uses a paired control over one compiled declaration.
Both `conditional-byte-array-get-*` fixtures statically retain
`ByteArray.get!`. The taken Boolean branch requires one `fap`, one `extern`,
and exactly one dispatch of that symbol. The skipped branch requires zero
executions of both forms and zero dispatches, while still requiring the static
external identity. This separates an honestly unreachable call site from a
misspelled or optimized-away requirement.

The FIR corpus requires an exact count for every statically required external.
Existing ByteArray reads, writes, size queries, natural addition, single
recorded effects, and signed-integer construction/classification now pin every
required symbol to one dispatch. The sequenced effect fixtures retain their
exact count of two, while the conditional skipped branch retains zero. Corpus
guards reject both a bounded-but-inexact external count and a required external
without a matching count obligation.

The same static/executed split applies to external identity, independently of
the generic `extern` instruction form:

- `externals` is the set of imported external names retained in the compiled
  artifact, checked against `requiredExternals`;
- `executed-externals` is the set of external names actually dispatched,
  checked against `requiredExecutedExternals`.

Set membership cannot distinguish repeated calls to one primitive from calls
to several different primitives. The runner therefore also emits
`executed-external-counts` as positive `{external, count}` records, with keys
that must exactly match `executed-externals`, and
`executed-external-trace` as an ordered JSON array containing one external name
per attempted dispatch. The harness requires all three views for every LCNF
result. It checks that the trace's distinct names reproduce
`executed-externals` and that its multiplicities reproduce
`executed-external-counts`; neither a set nor counts can conceal a reordered
sequence.
`requiredExecutedExternalCounts` supplies per-symbol
`{external, minimum, maximum}` obligations, and the coverage report retains
both per-case bound violations and corpus-wide required and observed totals.
When `requiredExecutedExternalTrace` is non-null, the observed sequence must
also match it element for element. All 27 current fixtures that retain an
external pin an exact trace: the skipped conditional pins `[]`, repeated
effects pin both occurrences, and the signed-integer fixtures pin construction
before negation or comparison.
The same exact-zero convention asserts that a statically retained external was
not dispatched on the selected path.

The LCNF backend also emits `missing-externals` and
`missing-executed-externals`.  The harness computes both missing sets itself,
requires all four diagnostics for every result, and rejects disagreement with
the backend.  Empty requirements therefore still collect explicit telemetry;
they do not make diagnostics optional.  This catches a fixture that still
contains some `extern` instruction but no longer retains or reaches the runtime
primitive it was meant to validate.

`external-events` reports the number of successful external calls captured with
event-time state.  Completion fails if that count diverges from the canonical
interpreter trace, preventing a missing snapshot from silently dropping a
projected semantic effect.

The report records per-case required, observed, and missing form and external
sets, dynamic form and external counts, ordered external traces, their
corpus-wide summaries, and interpreter step counts. Every LCNF result must emit
`executed-lcnf-forms`,
`executed-lcnf-form-counts`, `executed-lcnf-form-trace`,
`executed-step-trace`, `executed-externals`,
`executed-external-counts`, `executed-external-trace`, and a positive
`interpreter-steps` value, including cases whose executed requirement lists are
empty. An empty list means “collect telemetry without a path-specific
obligation”; it does not make the telemetry optional. Once a case lists an
executed form, count, or external, failing to reach it with the required
multiplicity fails validation just like a missing static obligation.
This distinction prevents code merely present in an unvisited branch from
satisfying an execution-coverage claim.  The checked corpus currently activates
at least one executed-form obligation for every case, and the Lean case type
has no default for that field: a new fixture must explicitly state its intended
path instead of silently inheriting telemetry-only coverage.  A second
compile-time guard requires the union to retain all 23 source-reachable forms
currently exercised in final impure LCNF, so removing a fixture cannot silently
lower corpus-wide instruction coverage.  Coverage failures and semantic
mismatches are independent signals: the harness still compares protocol
observations when an LCNF coverage obligation fails, and reports both findings
from the same run.

## Current corpus

The compiler-generated corpus currently has 97 cases.  Beyond literals,
branches, calls, closures, recursion, and ownership instructions, it covers a
heap-allocated natural above the tagged range, recursive structured-value
round trips, Unicode strings, maximum-width `UInt64`, portable `USize`,
polymorphic box/unbox, packed USize/scalar structure updates and `uproj`, and
nested tuple projection/reallocation. Five mixed-layout fixtures build one
source aggregate containing a heap natural, a newline/non-BMP Unicode string,
a packed byte array, maximum `USize`, and maximum `UInt32`. Independent
projections force the same compiler-produced constructor through object,
`USize`, and scalar storage paths, including absolute fixed-slot `uset`/`uproj`
coordinates after the three-object prefix.

The direct-LCNF corpus currently has one deliberately non-compiler-generated
case for the interpreter apply frame. Its distinct provenance suite and plan
prevent machine-only evidence from inflating source-compiler coverage.

Four adjacent-`USize` mutation fixtures use a two-object, two-`USize`,
one-scalar layout. Unique paths update absolute slots 2 and 3 while returning
the untouched neighbor. Shared paths retain the original alias, force
copy-on-write through the same slot-2 update, and independently return the
updated and original values. Their executed-form obligations distinguish the
unique path from the shared path's additional `inc` while retaining constructor,
object, USize, scalar, join, and decrement coverage.

Five multi-width scalar mutation fixtures use a one-object, one-`USize`,
15-byte scalar layout. Final LCNF packs the source fields in reverse byte
offsets: `UInt64@0`, `UInt32@8`, `UInt16@12`, and `UInt8@14`. Unique paths
update the first, middle, and last packed regions while returning an untouched
neighbor; shared paths update `UInt32@8` and independently return the updated
and original values. The same exact executed-form obligations cover object,
USize, and scalar copying around the changed region.

Five multi-object mutation fixtures complement those packed-field cases with
heap natural, Unicode string, and `ByteArray` fields in object slots 0–2,
followed by maximum `USize` and `UInt32` neighbors. Unique paths replace each
object slot and return a different heap neighbor, executing `oset` on the reuse
path. Shared paths replace slot 0 with a distinct heap natural and independently
observe the updated copy and retained original; their coverage excludes
`oset`, confirming that execution instead follows allocation and field-copy
semantics while the artifact still retains both branches.

Four aliased-`ByteArray` fixtures store one runtime child in two object slots
before the fixed-width neighbors. Unique paths replace slots 0 and 1 and return
both resulting children, checking that decrementing the replaced occurrence
does not invalidate its surviving alias. A shared path returns the updated and
original field pairs together. The final case composes object-slot replacement
with `ByteArray.set!`, retaining the surviving child while mutating it so the
child's own copy-on-write decision validates the reference count left by the
aggregate update. Its trace executes both `oset` and the external call.

Three self-replacement variants pass that same child as both the old and new
slot-0 value. They cover unique reuse, shared aggregate copying, and a composed
child mutation that must preserve the sibling alias. The unique traces execute
`oset`, including the external-mutation variant, while the shared trace takes
the allocation/copy branch. This makes increment/decrement ordering around
pointer-identical field assignment observable through the later child
copy-on-write result.

Two distinct-child swap fixtures exercise a simultaneous exchange of object
slots 0 and 1. The unique path returns the reversed `ByteArray` pair and carries
the first multiplicity obligation in the corpus: `oset` must execute at least
twice. Its retained telemetry observes exactly two writes. The shared path
returns both the swapped copy and original pair and executes no `oset`, instead
taking the allocation/copy branch.

The `multiplicity` tag groups seven fixtures with source-stable dynamic counts.
The two sequenced-effect cases require two dispatches of their specific
`recordImpl` or `recordByteArrayImpl` external, in addition to two generic
external/call forms. The recursive and local-tail three-element traversals
require four case/call steps and six object projections; reassociation requires
two decrements and sharedness checks plus four object writes; tuple rotation
requires two reuse decisions and four projections/writes; and the
distinct-child swap requires its two writes. Every one of these source-stable
counts now has equal minimum and maximum bounds, so losing or adding one
intended repetition fails coverage even when the same instruction form—or a
different external call—remains present and executable elsewhere in the case.

Stress fixtures additionally execute compiler-lowered ownership/reuse during
recursive reassociation, change the
tag of a uniquely reused constructor through `setTag`, delete a unique object
before allocating a larger replacement, retain 17 closure captures,
allocate/project a 70-object-field constructor, and match a nullary enum that
Lean lowers to a scalar discriminant.  Several fixtures carry exact provenance
into Lean's `tests/compile` suite at `v4.32.0-rc1`.  The corpus contains no
hand-written LCNF: the native and FIR paths consume the same Lean source
declarations.  Signed-`Int` fixtures cover both signs on either side of the
immediate 32-bit ABI boundary.  The boundary matrix independently validates
runner-supplied identity, compiler-built literals through `Int.ofNat` and
`Int.neg`, and constructor classification through `Int.decLt`, so tagged/heap
codec behavior, external results, and scalar-driven control flow cannot mask
one another.  Controlled `Nat.add` cases execute a real imported runtime
primitive with tagged inputs, a tagged-to-heap result transition, and a
heap-natural input/result.  Runner-supplied `ByteArray` identity, size,
indexing, and mutation fixtures validate the packed scalar-array heap ABI,
including scalar reads of zero, high-bit, and maximum byte values.
Out-of-bounds `ByteArray.get!` independently covers an empty array, the exact
end boundary, and a heap-natural index; native Lean, LCNF, and V8 must all
return the inhabited `UInt8` default zero.  Mutation
separately covers a unique in-place update and a shared copy-on-write update
that preserves the original alias.  The first controlled-effect case calls a
validation-owned `implemented_by` primitive: native Lean records the event it
actually executes, while the LCNF backend projects the matching external trace.
Both observations contain the ordered `validation.record` event with its
natural argument and result; no expected effect is stored as the oracle.  A
second case makes two data-dependent calls, requiring both backends to report
the exact sequence `7 → 8`, then `8 → 9`, as well as the final return value 9.
This distinguishes ordered semantic effects from the set-like instruction and
external coverage telemetry.  A heap-valued effect then performs two dependent
in-place ByteArray updates.  Native Lean and LCNF must preserve the original,
intermediate, and final byte arrays in the correct argument/result positions,
even though all runtime references point at the same uniquely owned location.

Protocol v2 encodes arbitrary `Nat` datum payloads as canonical decimal
strings; structural tags, widths, and bytes remain compact JSON numbers. This
keeps Lean's semantic type as `Nat` while making every backend observation
exact in Python and JavaScript. The protocol also has recursive data, signed
integers, scalar-bit, `USize`, output, and controlled effect fields. The LCNF
codec intentionally supports only the shapes needed by the checked corpus.
Immediate signed integers use
Lean's signed-32-bit payload ABI; larger values use the interpreter's semantic
signed-integer heap object.  Externally supplied packed constructors,
boxed-object arrays, and more effect shapes remain vertical slices with matching
native cases.  Tagged-natural and mutable ByteArray effect arguments/results,
packed byte-array identity, size, in-bounds and defaulting out-of-bounds
indexing, and unique/shared mutation are supported.  The LCNF adapter retains
immutable runtime snapshots immediately
before and after each successful external call, so heap effects are decoded at
event time rather than through potentially mutated or dead final-heap
references. The V8 adapter materializes the same schema-directed datums at the
Wasm import boundary and retains its own private event-time heap views.

The validation backend's external implementation is reject-by-default.
`Nat.add`, `Int.ofNat`, `Int.neg`, `Int.decLt`, `ByteArray.size`,
`ByteArray.get!`, `ByteArray.set!`, and the validation-owned Nat and ByteArray
effect recorders are currently allowlisted.  Natural addition decodes tagged or
heap operands, computes with Lean `Nat`, and re-encodes through the same
tagged/heap boundary as the interpreter.  The integer primitives decode and re-encode both the signed
immediate and heap representations; `Int.decLt` returns the scalar `UInt8`
discriminant consumed by lowered pattern matching.  Byte-array size reads the
packed heap object and returns a tagged natural; byte-array indexing returns
the selected packed byte as a scalar `UInt8`.  Byte-array mutation consumes its
array argument: unique cells update in place, while shared cells decrement the
consumed reference and return a newly allocated copy.  Validation-only guards
check both paths' locations, allocation counts, contents, and reference counts
in addition to the native observation comparison.  The Nat effect recorder
increments its argument; the ByteArray recorder updates its first byte.  Both
advance the interpreter world, and their event-time snapshots are decoded only
when selected by that case's projection metadata.  The native runner resets the
recorder before execution and drains it through a result-dependent hook, making
the effect ordering explicit even though the source-facing functions are pure.
`extern` must be present both statically and in executed-form coverage for every
runtime primitive fixture, while the matching name must independently satisfy
both external-name obligations.

## WebAssembly integration

The initial Wasm validation slice consumes the compiler track exclusively
through its public `compileValidationInvocation` API.  The integration-owned
`FirValidationWasm.lean` driver compiles each selected source entry through
`LCNF.main`; the shared API encodes corpus schemas and datums into semantic ABI
values, checks the result schema against the emitted result lane, and attaches
the invocation to the reusable module.  It emits deterministic `.wasm` and
ABI-manifest products only for that ordered selection and checks that each
module exactly exports its source entry.  Manifests may include the encoded
initial FIR runtime and semantic imports needed by heap-backed invocations;
the driver does not modify or add policy to `Fir/Wasm`.

The external adapter then loads those exact retained bytes in Node's real
`WebAssembly` engine.  It and the Talos artifact runner consume the same
semantic host module for initial-runtime reconstruction, opaque handles, ABI
lane conversion, and imports.  Schema-directed decoding cross-checks each
manifest argument against the corpus datum before invocation and converts the
semantic result back into the shared backend protocol; unsupported schemas
fail closed.  The binary's imports must exactly match the compiler manifest.
The runner receipts the provider bundle identity and both per-case products.
The checked suite includes all five scalar maxima, parameterized
maximum-value round trips for `UInt8`, `UInt16`, `UInt32`, `UInt64`, and
`USize`, plus a nonempty `List Nat` containing a heap natural.  That last case
reconstructs the initial constructor graph and executes the compiler-produced
`getTag` import before returning `UInt64`.  Sibling nonempty and empty cases
return Lean 4.32's unboxed Boolean as `uint8`, covering both one and zero; the
LCNF and V8 schema decoders accept only those values for that representation.
The first W5 additions compile a dependency-bearing polymorphic box/unbox call
and a packed constructor initialized through `uset`/`sset`, projected through
`uproj`, and released through `dec`.  Source artifact compilation retains
captured helpers internally while exporting only the selected entry.
Compiler-generated direct calls, captured and underapplied closures, recursive
empty and traversal paths, and an exact `Nat.add` external now run in V8 as
well.  A heap-backed Unicode `String → String` round trip retains the
compiler-produced ownership increment and returns the reconstructed string
through the semantic host.  Signed `Int` identity programs cover positive and
negative immediates, both exact 32-bit boundaries, and the first positive and
negative values represented by heap integer objects.  A heap-backed
`ByteArray → ByteArray` identity preserves zero, signed-boundary, and maximum
byte payloads.  Exact `ByteArray.size` and `ByteArray.get!` external handlers
also cover zero, high-bit, and maximum-byte reads without changing heap state
or world.  `ByteArray.set!` covers both ownership paths: unique arrays update
in place, while shared arrays preserve the original and allocate the updated
copy.  The independent artifact corpus separately compares external
world/trace effects and a two-call lazy-cache hit/miss sequence against Talos.
Compiler-generated `Int.ofNat` and `Int.neg` calls construct positive and
negative literals at both immediate/heap representation boundaries.
The default native-to-V8 matrix covers all 95 corpus cases, including a natural
above `UInt64`, a recursive list containing that value, tagged-to-heap
`Nat.add`, heap-input `Nat.add`, all three controlled-effect programs, and all
five mixed-layout projections. `make validate-v8` delegates whole-corpus
selection to the plan rather than maintaining a second case allowlist, so every
new shared fixture enters the real-engine triangle by default.
`FIR-BUG-wasm-none-json-nat-precision` records the protocol-v2 exact-decimal
repair.
Native Lean remains the source oracle.
Talos can subsequently consume the exact same module and inputs, with V8 as
the reference Wasm engine:

```text
native Lean <-> V8          compiler/runtime validation
native Lean <-> FIR LCNF    LCNF semantics validation
V8          <-> Talos       Wasm interpreter validation
```

Successful lowering or encoding is preparation, not semantic validation.
Adding either backend is a registry extension implementing the existing
build/execute/audit adapter contract; it does not change comparison semantics
or the native-owned corpus.  Wasm-specific compilation and engine telemetry
belong in that adapter's optional audit, just as instruction/external coverage
belongs to the LCNF adapter today.
