# Talos consolidation evaluation, 2026-10-08

Evaluated against FIR `15dc1f460` on `root/talos-consolidation`.
The coordinator is the existing `meta` session, routed as `fir/root`;
the evaluation session is registered as `fir/talos-consolidation`.

## Decision

Consolidate on Lean and mathlib **4.34.1**, which accepted FIR already uses.
Evaluate an immutable upstream Talos commit rather than maintaining the
old toolchain patch, but do not adopt the current candidate as a pin-only
change: its FIR proof cone fails. There is no upstream release or tag to
call the “latest stable Talos release.” GitHub's releases and tags APIs
both returned `[]` on the evaluation date. The official repository describes
Talos as work in progress with changing APIs and proof interfaces.

The newest upstream main observed was
[`80644390de3ad4db3055445259a034413ae41577`](https://github.com/cajal-technologies/talos/commit/80644390de3ad4db3055445259a034413ae41577),
dated 2026-10-06. Its interpreter selects Lean `v4.34.1` and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` without a patch.
The native toolchain migration landed in
[`64690614e85096ba631644a27dc4ac361bfe192a`, PR #262](https://github.com/cajal-technologies/talos/pull/262).
Treat `80644390` as a migration candidate, not an accepted or upstream-certified
stable dependency.

## Existing supported path

`make talos-setup`, `make talos-check`, `make proof-trust`, and CI select
`tooling/talos-434`, backed by worktree-local `.deps/talos-434`.
Its authenticated Talos pin is `0e05edbcfbb105b33e90c60b4f50e2cf193d9254`;
`talos.patch` changes its original Lean/mathlib 4.33 pins to 4.34.1.
The compiler identity is `5045d0056413266e57c625dcd7c365b10e377c52`.
The tracked manifests and source hashes are checked by setup and check scripts.

Blueprint consumes this exact prepared FirTalos project, including a tracked
path manifest. The retained-initializer gate also prepares and consumes it.
The W7 artifact package depends on FIR and does not itself require Talos.
Changing the Talos setup layout therefore affects Blueprint and retained
initializers even when the ordinary FIR build remains unchanged.

## Candidate compatibility evidence

An isolated `.deps/talos-candidate/project` copies the unchanged accepted
FirTalos sources and uses the exact upstream candidate interpreter and manifest.
It uses the repository's toolchain-scoped Lake cache, with all mutable package
and build state local to this worktree. No candidate patch, tracked pin change,
symlinked build state, or change to another lane's proof files was made.

The focused batch command is:

```sh
lake -d .deps/talos-candidate/project build \
  FirTalos.Adapter FirTalos.ConcreteResidentFloat FirTalos.Correctness.Execution
```

`FirTalos.Adapter`, `FirTalos.Runtime`, `FirTalos.Differential`, and
`FirTalos.Correctness.Adapter`, `FirTalos.Correctness.Execution`,
`FirTalos.ConcreteResidentMemory`, and `FirTalos.Correctness.Composition`
compile against the new interpreter.
The dependency cone fails at
`FirTalos.Correctness.locals_set?_exists`,
`integration/talos/FirTalos/Correctness/Locals.lean:146,148`:
`Wasm.Locals.validIndex` no longer exists upstream. Upstream removed the
definition `i < s.params.length + s.locals.length` and its unchecked setter;
the checked `Locals.set?` remains. There are 161 textual references to
`validIndex` across eight accepted FIR proof files, including resident Nat,
Nat multiplication/subtraction, USize, big-numeric, and compiler-correctness
proofs. A narrow W6-owned migration is needed; duplicating an upstream
definition under its old namespace would conceal the dependency change.

The combined command exits 1; the Float target remains blocked behind the
failed Locals dependency, while the Execution target passes. The full
umbrella, trust audit, retained initializers, Blueprint build, and linked
artifact checks have not been accepted against the candidate. The focused
failure is sufficient to reject an immediate pin-only migration.

The local failure log is
`.deps/tool-logs/talos_candidate_build_.bVWr3S.log`, SHA-256
`bd76dd994be1bc54c1b609ee3f4e48f0a781adb67cdc02c45f3c6a7e5664ca82`.
The upstream CI log is `.deps/talos-upstream-ci.log`, SHA-256
`1810eb9a68082fdbf06e259b5ee6249d254c6fd693667bc08e0d1abe7de4d62d`.
These logs are disposable working evidence; this document preserves the
decision and exact failing invariant.

Evaluation checkpoint checks: `make check` passes, including overlay setup
identity tests, V8 and direct-LCNF validation, trust source/profile negatives,
and mailbox tests. `scripts/mailbox check` passes. This is a documentation-only
checkpoint; the official Talos gate was not rerun and no fresh acceptance of
the old or new Talos proof umbrella is claimed.

The upstream delta contains 65 commits and changes 83 interpreter files
(7,258 insertions, 4,559 deletions). Review-sensitive changes include:

- Floating operations switch from native `Float32`/`Float` to an integer-ratio
  IEEE754 model. Existing Float proof normalization is not evidence that all
  new arithmetic definitions match the accepted runtime observations.
- `wp_load32_cons` gains an i64-address case, and scalar small-step loads/stores
  use `memoryAddress?`. Existing concrete memory proofs need checking.
- `Instruction.select` gains an optional result annotation and `localTee`
  becomes a first-class instruction. FIR's adapter compiled, but exhaustiveness
  and proof-side instruction reasoning still belong to the complete gates.
- Validation tracks initialized non-defaultable locals, checks table
  declarations, and validates typed/untyped select. These change the target
  admission relation consumed by FIR, even without a new FIR instruction.
- Small-step `RuntimeEnv` gains module instances and linking. FIR's structured
  machine currently delegates atomic operations to `execOne`; inspect its
  complete proof cone rather than assuming every linking API is consumed.

Upstream's [proof/smoke workflow](https://github.com/cajal-technologies/talos/actions/runs/37463782938)
succeeded for the candidate. The
[V8 differential workflow](https://github.com/cajal-technologies/talos/actions/runs/37463783118)
failed. Its final errors list ten stale baseline exceptions for cases that now
agree with V8 or are no longer generated; the report totals are 566 agree,
22 sut-reject, 27 SOUNDNESS, and 5 sut-unsup. Those totals alone do not prove
new regressions. This is not all-green upstream evidence, and the existing
known-gap inventory must be assessed against FIR's emitted subset before
acceptance. No semantic workaround was attempted and no new FIR semantic bug
is claimed by this evaluation.

## Cleanup scope

| Item | Evaluation and action |
| --- | --- |
| Old standalone Talos setup/attestation wrapper | Already retired in `eef7290a81e3ae1b23a3f64afe636f467847d960`; do not repeat. |
| `integration/talos/{lean-toolchain,lakefile.toml,lake-manifest.json}` | Already removed in `6ec5a05d2`; preserve the active proof sources and oracle. |
| `tooling/talos-434/talos.patch` | Remove only with an accepted native-4.34.1 upstream migration; remove its obsolete hash/fixture wiring coherently. |
| Overlay manifests and identity checks | Regenerate/authenticate for the exact accepted candidate; preserve fail-closed identity and source-mirror checks. |
| `float-normalization.patch` | Separate local proof normalization, not an old release. Retest and obtain W6 review before changing its pinned source hashes or retiring it. |
| `tooling/talos-434/README.md` | Still calls the removed standalone manifest historical. Correct when root adopts a documentation successor. |
| `integration/talos/README.md` introduction | Still describes 4.33 and waiting for PR #172, which is now closed unmerged. Correct through root/W6 coordination. |
| Blueprint contribution chapter | Contains the current older Talos pin; update with the adopted pin and evidence. |
| `lean433UpstreamBridge` | Intentional audited axiom name, not a selectable old compiler. Validator supports only the accepted 4.34.1 profile; do not rename as cleanup. |
| `retainedRC2` and `RetainedRC2` names | Historical package/library names; their gate consumes the accepted root toolchain. Names alone are not evidence of obsolete execution. |
| Other 4.33/RC2 integration toolchain files | Separate consumer recipes: Verso flat/html, Illuminate hit/spatial/LLVM, and VBP viewer/resolver/native probe. Inventory and migrate or retire through their owners; this Talos result does not establish that they are unused. |
| Old worktrees, installed toolchains and generated releases | No deletion performed. Establish active consumers and a concrete retention list before destructive cleanup. |

## Migration acceptance boundary

Root records an exact candidate and leases the eight affected W6 proof files
before implementation. Adapt the explicit local-index premises without weakening
them, then rebuild the complete proof cone to discover additional failures.
Keep the accepted fallback until the candidate gates pass.

The resulting integration checkpoint must run `git diff --check`, `make check`,
worktree-local `make talos-setup`, `make talos-check`, the focused Float and
changed proof cone, and the full trust audit. Validate Blueprint against its
refreshed path manifest and the retained-initializer consumer using immutable
lean-zip inputs. A changed Talos semantic contract also requires
`bash integration/talos/artifact/check.sh`, including browser checks through
`FIR_BROWSER`, before root's integration acceptance. Resolve or explicitly
review the upstream red differential evidence rather than calling it green.

Publish one clean exact root-reviewed checkpoint. Only after acceptance should
the old compatibility patch and its tests be retired. Remote publication and
worktree/toolchain/generated-state deletion are separate actions.
