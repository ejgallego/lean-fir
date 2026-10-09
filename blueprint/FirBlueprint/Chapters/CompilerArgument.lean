import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6
import FirBlueprint.RetainedInitializerScene

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The compiler argument, from a concrete call to a theorem" =>
%%%
tag := "compiler-argument"
%%%

A compiler should preserve what a program does. Here the first promise is
precise: if the source program returns successfully, its compiled Wasm export
also returns, with the same represented result and observable effects of
external operations, in the same order. The proof must connect actual executions and keep the export's chosen
result representation throughout calls and returns. Conditional versions of
this argument are checked; the complete compiler guarantee still has open
obligations.

The current strategy starts with selected programs and their real semantic
blocks. A theorem for one fixed program must cover every allowed input and
related entry state. Proving those instances independently can reveal the
invariants needed for a general compiler theorem. Once the general theorem
exists, the same instance statements can follow by specialization. We begin
with an initializer in a captured program, for which a local execution and
caller-preservation proof already exists.

# A call that must return to its caller

The captured program contains `RetainedRC2.initializer`, a function taking no arguments. It
creates an Array with capacity five, pushes tagged zero into it, and
returns the resulting singleton Array. Consider a supported caller whose next
let binding invokes this initializer. The caller must eventually bind the
result to its destination and continue with its saved environment, control
points and continuation frames.

The initializer is lazy: its result can be cached in a runtime global. We take
the cold-cache case, where that global is absent and the body must execute.
After the body returns, publication caches the result and marks its reachable
heap graph persistent, protecting its cells from ordinary reuse. Only then can the source caller bind the result and
resume. This is a useful test of correctness: representing the returned Array
alone would not explain why publication preserves the caller's saved heap facts.

This proof covers every related supported caller satisfying its stated
contracts, rather than a finite list of test heaps. It establishes a local
block for the initializer in the captured program. Whether the selected
`compressStored` export reaches this block, and correctness of that whole
export, require further arguments.

# The source program and the two machines
%%%
tag := "w6-machines"
%%%

The source of this proof is Lean's final intermediate representation, impure
LCNF, captured as a FIR program $`p`. It makes representation, allocation,
mutation and ownership operations explicit. A source configuration $`\sigma` contains the program, current code
or yielded/call control, an environment mapping variables to values, join
points, continuation frames and runtime $`r`. The runtime contains a heap,
globals, world, ordered external trace and a cursor for fresh source locations.
This machine is the semantic boundary captured from Lean's compiler; a proof
relating the original Lean source to that capture is a separate bridge.

{name Fir.LeanIR.Impure.executeStep}`executeStep` can advance to another state,
return an observation, or report a semantic fault. Write
$`\sigma\leadsto_s\sigma'` when it returns `.next` $`\sigma'`, with the source
external implementation $`\varepsilon` fixed. This implementation supplies the
semantic responses to source calls such as `Array.mkEmpty` and `Array.push`. The finite path notation
$`\sigma\overset{n}{\leadsto}_s\sigma'` abbreviates
{name Fir.LeanIR.Impure.ExecSteps}`ExecSteps` with exactly $`n` successful steps.
Neither a source step nor a finite path asserts eventual termination.

## The target package, export and result ABI

Compilation selects an export name $`e` and its source entry. The target runs
a compiled Wasm module together with host functions that implement its imports.
The supported-export specification supplies the compiler's symbolic module,
the Wasm module produced by its adapter, and the resolved host environment.
Write $`M` for these existing arguments. Host contracts specify the behavior
required of imported operations; this is the contracted package proved here.
Resident linking and released bytes need additional correspondence proofs.

The concrete target configuration $`\tau` contains a Talos store $`S`, locals,
running/branch/return/halted control, and block, loop and call frames.
{name FirTalos.Correctness.StructuredWasmStep}`StructuredWasmStep` exposes emitted
control flow while Talos executes atomic instructions and imported calls.
Write $`\tau\overset{m}{\longrightarrow}_M\tau'` for exactly $`m` such steps in
the adapted module and resolved hosts. A source operation can require several
target instructions; an administrative source step can require none.

The export also fixes a result application binary interface (ABI) kind $`A=\mathrm{spec.sourceResultKind}`:
it is the agreed encoding of the source result as a physical Wasm value.
An initializer may return an object while its caller ultimately returns at a
different kind. The root of the execution remembers the original export's
$`A` across these calls. Choosing a convenient new ABI at the end would change
the guarantee.

Interpreter fuel bounds a runner; it is neither a semantic fault nor a shared
clock for the machines. The successful-return theorem starts from a finite
successful source evaluation and derives a sufficient target execution. It
makes no claim that every source input terminates.

# Observations and the representation carried through a call
%%%
tag := "w6-rooted-relation"
%%%

A returned source observation $`o` records a value $`v`, heap, world and ordered
external trace. The world records the observable state of external operations;
the trace records their names, arguments and results in order. Globals and the fresh-location cursor are runtime components
outside this public observation. Exact observation identity therefore keeps
these observable fields but does not identify every runtime field.

Source heap locations and concrete byte addresses are different coordinates.
A refinement witness $`w` records how source values and live heap objects are
represented in target values and memory. At one state the same witness also
relates globals, world and ordered trace. Each witness satisfies the relation's validity requirements, including
lookup-visible injectivity: distinct source locations visible through the
witness have distinct represented target addresses. A successor may use a new witness. No extra
cross-phase equality, fixed physical address or monotone extension law relates
all the phase witnesses.

The execution relation must retain more than this value correspondence. It
also records validated current code, generated continuations, caches and saved
caller information. For fixed $`p,M,\varepsilon,A`, use the abbreviations

$$`\begin{aligned}
R_{A,w}(\sigma,\tau)&\equiv\operatorname{Rooted}_A(w;\sigma,\tau),\\
R_A(\sigma,\tau)&\equiv\exists w,\ R_{A,w}(\sigma,\tau).
\end{aligned}`

Here $`\operatorname{Rooted}_A` is the existing
{name FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt}`ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt`
with those fixed arguments. This notation introduces no new invariant. Its
existential form is the relation used by
{name FirTalos.Concrete.ConcreteStructuredCompilerCurrentStepAdmission.toRootedTraceSimulation}`toRootedTraceSimulation`.
The current callee's ABI may differ from $`A`; saved rooted facts retain $`A`
until the final export return.

The entry contract relates encoded parameters to the source environment,
heap/runtime, reuse capacities and caches. The compiler constructs the rooted
control relation from this contract. The client supplies related entry data;
the proof derives intermediate states and future target paths.

# The precise successful-return guarantee
%%%
tag := "w6-notation"
%%%

We can now state the property the compiler should establish. For a source
observation $`o` and value $`v`, abbreviate successful evaluation by

$$`\begin{aligned}
\sigma\Downarrow_{\varepsilon}(o,v)\equiv{}&
\operatorname{ExecEvaluates}(\varepsilon,\sigma,o)\\
&\land\ o.\mathrm{outcome}=\operatorname{returned}(v).
\end{aligned}`

Keep $`p,M,e,A` fixed through the selected supported-export
specification, with $`A=\mathrm{spec.sourceResultKind}`. Its context and source
code determine the source entry. Fix the source external implementation
$`\varepsilon` subject to the retained contracts below. This property uses the observation-facing
conclusion of {bpref "conditional-return"}[].

For each invocation, quantify a source
entry runtime $`r_0`, environment $`E_0`, concrete store $`S_0`, initial witness
$`w_0`, physical parameter row $`\bar u`, reuse facts and finite byte budget.
Require the following entry and execution conditions:

* *External/resource contracts:* the reviewed source primitive and installed
  implementation contracts, whose general coverage remains incomplete where
  documented. Finite-resource bounds and address-space safety remain explicit
  execution conditions.
  Neither follows from static validator acceptance.
* *Cache alignment:* the compilation context's cached declarations equal the
  program's cached declaration names.
* *Arity:* $`|\bar u|=\mathrm{spec.targetFunction.numParams}`.
* *Related entry:* the existing
  {name FirTalos.Concrete.ConcreteReuseCapacityCacheAbiFrame}`ConcreteReuseCapacityCacheAbiFrame`
  relates $`r_0,E_0,S_0,w_0`, the reuse facts/budget and the parameter-derived
  target locals, including its cache/reuse/closure ABI conditions.

Let $`\sigma_0` be the source code-entry state from this runtime/environment.
Call the resulting program property $`P_{\mathrm{success}}(p)`. In words, every
allowed invocation that returns in the source must have a matching actual
export return. The required conclusion is

$$`\begin{aligned}
&\forall o,v,\quad\sigma_0\Downarrow_{\varepsilon}(o,v)\\
&\quad\Longrightarrow\exists r,\quad
o=\operatorname{ReturnedObservation}(r,v)\\
&\qquad\land\ \operatorname{Return}_{M,e}(S_0,\bar u;r,v,A).
\end{aligned}`

The last predicate is only an abbreviation for the existing exported
termination predicate, with all invocation arguments shown:

$$`\begin{aligned}
&\operatorname{Return}_{M,e}(S_0,\bar u;r,v,A)\equiv\\
&\quad\operatorname{ConcreteExportTerminatesWith}\\
&\qquad\bigl(M.\mathrm{env},M.\mathrm{wasm},e,S_0,\bar u,\\
&\qquad\quad\operatorname{RefinedReturnPost}(r,v,A,[])\bigr).
\end{aligned}`

$`M.\mathrm{env}` is the resolved host environment `hosts.env`, and
$`M.\mathrm{wasm}` is the adapted module's `wasmModule`.

$`P_{\mathrm{success}}(p)` means that this
statement holds for *all* its allowed invocations: fixing the program does not
fix the input. It preserves every finite successful source evaluation and
derives actual target export termination. It asserts no source totality. The
empty list is the exported invocation's caller operand tail. The existing
{bpref "return-post"}[] uses one terminal witness and physical value to relate
the complete runtimes and exact result ABI, clear the target failure channel,
and produce the singleton return stack. That witness need not equal $`w_0`.

The displayed conclusion is exactly the wrapper's shape, with the fixed
arguments abbreviated. The existing conditional proof chooses $`r` to be
the actual source final runtime; observation equality alone records value, heap, world and trace,
without identifying globals or the location cursor. The stronger path-resolved
internal result is proof evidence, not an extra public conclusion.

This property definition adds no Lean declaration. The fixed
Stored instance and eventual general compiler theorem remain open.
{bpref "conditional-return"}[] proves this conclusion *conditionally* on
uniform current-step admission and address-space safety. Current-step admission
is the semantic law supplying the argument/result representation, operation
behavior and resource-accounting facts needed at each supported validated
operation. Address-space safety is a separate law. That route must
construct compiler-owned admission; address-space safety remains an explicit
execution condition. Admission, reached-state provenance and
heap-miss preservation are not hidden in the allowed entry clauses above.

# Follow the initializer through its actual states
%%%
tag := "worked-retained-initializer"
%%%

Return to the initializer call. Let $`d` be the caller's let destination and
$`k` the code that follows that binding. The caller environment $`E`, join
points $`J` and continuation frames are saved while the initializer runs. Write
$`F_s,F_t` for its saved source and target frame stacks, respectively, and
$`i` for the target local corresponding to destination $`d`.
A join point is a local control destination; restoring the caller must restore
these control facts as well as its variables.

Two entries matter. The caller has a historical runtime/store/witness anchor
$`(r_h,S_h,w_h)`. The initializer's construction starts at the current
$`(r_0,S_0,w_0)`, which may be later. Set
$`c=r_0.\mathrm{nextLocation}`: this source-location cutoff stays fixed for the
whole construction. The new Array is allocated at $`c`. The tracked saved reuse-token locations
are below it, by the related entry's semantic heap facts. It is not a concrete byte address and need not equal the caller's
historical cutoff. A concrete address such as $`a` belongs to target memory.

Write $`\operatorname{heap}(c)` for the source value referring to heap location
$`c`. The caller may have retained reuse tokens: a tracked variable contains a
token naming an older source cell and has a separate retained-capacity fact.
The tracked cell must remain ordinary (nonpersistent) for the saved reuse facts
to hold. Publication must preserve those facts. An *owned edge* is a heap-reference field whose
ownership the parent retains. Owned reachability follows such edges from a
root, including sharing and cycles. Tagged zero is immediate data and creates
no heap edge. Here the new Array's only element is tagged zero, so the returned
graph stays entirely at or above $`c`. More generally, region closure means
that every owned edge from any parent at or above $`c` stays at or above $`c`.
This prevents publication of the fresh graph from reaching an older saved token.

The following states and diagrams describe the conditional proof family. They
assume a related supported caller with a cold cache, the specified source
Array laws, installed host-handler laws and enough finite allocation headroom.
Let $`B` be the caller's byte budget and
$`\Delta=\operatorname{residentArrayAllocationBytes}(5)` the physical cost of
the five-slot Array. The precise contracts follow after the pictures.

:::table +header
*
  * Milestone
  * Source state
  * Concrete target and representation
*
  * Caller before the call: step 0
  * Code is the let binding of the initializer to $`d`; environment, joins and caller frames are saved. The cache is cold.
  * Validated generated lazy-call code and related locals/store. The original root ABI is $`A`.
*
  * Cold callee entry: step 2
  * Initializer code starts with empty local environment. Cache and destination-bind frames sit above the saved caller frames.
  * The emitted call/label continuation is installed. The active construction scope is anchored at $`r_0,S_0,w_0` and cutoff $`c`.
*
  * Six body steps completed: step 8
  * The two literals, empty-Array call/bind and UInt8 boxing have run. The empty Array is at $`c` with capacity five, boxed tagged zero is bound, and the runtime is `afterMkEmpty` applied to $`r_0`.
  * Allocation derives a witness $`w_1` mapping $`c` to a concrete address $`a`. A physical word $`z` represents tagged zero; its numeric encoding is not assumed.
*
  * Initializer's local return: step 12
  * Three push steps and one return complete the ten-step body. The Array now contains one tagged zero; the runtime is `afterPush` applied to $`r_0`. Cache/bind frames remain above the caller.
  * The fresh in-place push stores $`z` without a second allocation. The local-return fact supplies a physical result $`q` representing the heap object at $`c`, under the produced witness, and retains the original construction region.
*
  * Publication: step 13
  * The yielded heap object at $`c` is cached and marked persistent. Its source destination-bind frame is still pending.
  * Publication executes cache/global updates and reloads the result representation. Caller target locals/frames are already restored, with the result on the operand head and destination `local.set` pending. The rooted relation at $`A` and `HeapRegionClosed c` hold.
*
  * Caller resumed: step 14
  * Bind $`d` to the heap object at $`c` and continue with $`k`. Joins and caller frames are exactly the original ones.
  * Execute the destination `local.set`; the original target frames remain restored. The validated caller relation has the updated environment/global, budget $`B-\Delta` and only $`d`'s old reuse fact erased.
:::

The runtime definitions
[`afterMkEmpty` and `afterPush`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L59)
append the two ordered events `Array.mkEmpty` and `Array.push`, with their exact
source arguments/results. The primitive responses preserve world. Publication
changes the global/persistence state; binding changes the environment. This
local return has cache/bind frames and is not a completed export evaluation.

## Source and target at four proof checkpoints

These native Illuminate panels depict a *symbolic family of theorem
checkpoints*, not a sampled execution or a universal proof. Assume the related
supported caller/root, cold cache, source primitive laws, installed handler
laws and $`\Delta\le B` described above and specified below. Each panel's derived facts are
conditional on those inputs. The figures use schematic layout coordinates;
source locations and concrete byte addresses have separate meanings.

Both entry anchors, cutoff $`c` and original export ABI $`A` stay fixed.
Phase-indexed witnesses such as $`w_{12},w_{13},w_{14}` and corresponding
addresses are existential; the panels
do not assume a generic equality or extension law between them. The physical result $`q_{13}` represents the returned Array; the word
$`z_{13}` represents its tagged-zero element. These are different roles. A drawn saved token $`\ell` stands for any tracked source location, if one exists.

*Step 2 — cold entry.* The saved cache/bind and generated call/label
continuations are installed; no fresh object mapping is asserted yet.
The entry segment takes three target steps.

```diagram
FirBlueprint.RetainedInitializerScene.entered
```

*Step 12 — local return.* Ten body source steps have produced the singleton
Array and a fresh-yield relation. The tagged element is data, with no owned
heap edge. The body target-path length $`T` is existential.

```diagram
FirBlueprint.RetainedInitializerScene.returned
```

*Step 13 — publication.* The source still has its callee environment/joins
and pending bind capturing caller $`E,J`. The target has already restored
caller locals/frames and reloaded $`q_{13}`; only its destination `local.set`
remains pending. This is the thirteen-step theorem's rooted/closed endpoint.
Publication contributes seven target steps.

```diagram
FirBlueprint.RetainedInitializerScene.published
```

*Step 14 — caller resumption.* The companion theorem restores source
$`E[d\mapsto\operatorname{heap}(c)]`, caller joins and frames. The target writes
the corresponding local index $`i` in one step; its frames remain restored.
The public fourteen-step result exposes validated caller restoration, without
a separate final `HeapRegionClosed` conjunct.

```diagram
FirBlueprint.RetainedInitializerScene.resumed
```

# The common assumptions of the two local theorems

Fix
$`p=\mathrm{RetainedRC2.program}`, its captured initializer, a supported compiled
package $`M`, source external implementation $`\varepsilon` and original root
ABI $`A`. The two statements below then quantify **every** supported caller
row and related source/target state $`\sigma,\tau`: caller context/function,
active function ABI and expected caller result, label context, historical entry
$`(r_h,S_h,w_h)`, current runtime/store/witness $`r_0,S_0,w_0`, source environment
$`E`, target locals/code, retained reuse-capacity facts $`F`, byte budget $`B`, destination $`d`
and continuation $`k`. Fixing the captured program does not select a finite
family of caller heaps or inputs.

Write $`\mathcal V` for the existing validated current-code relation at this
caller row and let binding. It abbreviates
{name FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome}`ConcreteStructuredValidatedCodeOutcome`
with all those indices. The allocation cost $`\Delta` is
{InlineLean.lean}`Fir.Wasm.Concrete.residentArrayAllocationBytes 5`, with the
construction cutoff $`c` fixed at the current entry as above.

:::table +header
*
  * Retained premise
  * Meaning in this example
*
  * Supported caller and validated current relation
  * A supported caller specification and $`\mathcal V` relate the actual compiled/adapted function, current let and saved frames. Active-result equality and root agreement retain $`A`, even though the initializer returns an object. The let value is exactly the nullary application of the captured initializer.
*
  * Cold cache
  * The initializer is absent from the source runtime globals. This proof takes the cache-miss branch.
*
  * `FreshArrayExternalContract`
  * Uniform source laws specify empty allocation and the fresh empty-receiver push branch with spare capacity and a tagged element. The actual calls use capacity five and payload zero; wider Array behavior is outside this contract.
*
  * Installed concrete handler laws
  * The empty handler conforms at $`S_0,w_0` for every related capacity-five request. The push law quantifies every concrete runtime/witness related to `afterMkEmpty` $`r_0`, every mapped address of $`c`, every word representing tagged zero, and every request with the exact `Array.push` name/arguments. It concludes the in-place handler equation. Source laws alone do not establish these implementation equations.
*
  * Finite headroom
  * $`\Delta\le B`, where $`B` is the related allocation budget. Boxing and this push branch allocate no additional physical bytes.
:::

The client supplies neither a source execution nor a target path. Callee
support, generated cache/continuation facts, the five binding-kind lookups and
the post-body resource scope are derived inside the proof. The handler laws
remain contracts for the installed concrete host; they do not prove execution
of a resident W7 helper or JavaScript implementation.

# Publication and caller resumption are separate conclusions

The accepted source theorem
[`rootedLet_publishesAtBind`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1016)
derives thirteen source steps, an actual finite target path, the rooted relation
at the original export ABI, and closure of the fresh heap region. Its
[`rootedLet_publishes_and_resumesCaller`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1100)
companion adds the destination bind and derives the fourteen-step restored
caller. The latter statement exposes caller restoration rather than a separate
final region-closure conjunct. These are reviewed accepted theorem sources;
this exposition adds no Lean association or fresh retained-initializer proof
build. Their statement/proof files at `f6850d79f` are unchanged at the `8cd93fd45`
exposition base.

## Publication after thirteen source steps

**Conclusion.** For every caller row and initial pair $`\sigma,\tau`
satisfying *all* the named hypotheses above,

$$`\begin{aligned}
&\exists m,w',\sigma',\tau',\quad
\sigma\overset{13}{\leadsto}_{s}\sigma'\\
&\quad\land\ \tau\overset{m}{\longrightarrow}_{M}\tau'\\
&\quad\land\ R_{A,w'}(\sigma',\tau')
\ \land\ \operatorname{Closed}_c(\sigma'.\mathrm{runtime.heap}).
\end{aligned}`

Here $`\operatorname{Closed}_c(h)` abbreviates the *whole*
{name FirTalos.Concrete.HeapRegionClosed}`HeapRegionClosed` $`c\ h` predicate:
every owned heap-reference edge from a
parent at or above $`c` leads to a child at or above $`c`. Closure concerns all
such parents, not just the returned root. The rooted relation has the same
fixed $`p,M,\varepsilon,A` and the existential *final* witness $`w'`.

**Reading and correspondence.** The exact source count is thirteen; the target
count, final states and witness are derived existentially. This is the exposed
conclusion of the source-reviewed
[`rootedLet_publishesAtBind`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1016),
with Lean arguments abbreviated. Its construction additionally identifies the
published global and yielded root $`\operatorname{heap}(c)`: the source bind
is pending while the target caller frames are already restored and its
destination `local.set` is pending. Those are facts of the constructed
endpoint, rather than extra conjuncts of the displayed top-level signature.

## Caller resumption after fourteen source steps

Define the source runtime abbreviation

$$`\begin{aligned}
\operatorname{Pub}(r_0)\equiv{}&
\operatorname{setGlobal}\bigl(\operatorname{afterPush}(r_0),\\
&\qquad\mathrm{initializer},\operatorname{heap}(c)\bigr).
\end{aligned}`

It means the actual `afterPush` runtime with the initializer global set to the
source object value at $`c`. The notation $`\operatorname{heap}(c)` denotes
that source *value*, not the location by itself. Let $`\mathcal V'` abbreviate
the same validated caller relation with the following indices:

:::table +header
*
  * Preserved indices
  * Updated indices
*
  * Historical entry $`r_h,S_h,w_h`, caller context/function, labels, active ABI and expected result
  * Facts $`\operatorname{eraseFact}(F,d)`; budget $`B-\Delta`; runtime $`\operatorname{Pub}(r_0)`; environment $`E[d\mapsto\operatorname{heap}(c)]`; continuation $`k`
*
  * Compiled package and source implementation
  * Existential target store $`S'`, locals $`L'`, remaining target code $`C'`, witness $`w'` and states $`\sigma',\tau'`
:::

$`\operatorname{eraseFact}(F,d)` abbreviates
{name Fir.Wasm.eraseReuseCapacityFact}`eraseReuseCapacityFact` at the
let destination. For a witness $`\nu:\mathcal V'`,
$`\operatorname{RootAgreement}_A(\nu)` abbreviates
{name FirTalos.Concrete.ConcreteStructuredValidationAgreesAtRoot}`ConcreteStructuredValidationAgreesAtRoot`
for $`\nu`'s agreement and validated
frames. $`A` stays fixed in the ambient root assertions, rather than indexing
$`\mathcal V'`; it is not changed to the initializer's object ABI.

**Conclusion.** For every caller row and initial pair satisfying the *same*
named hypotheses,

$$`\begin{aligned}
&\exists m,S',L',C',w',\sigma',\tau',\quad
\sigma\overset{14}{\leadsto}_{s}\sigma'\\
&\quad\land\ \tau\overset{m}{\longrightarrow}_{M}\tau'\\
&\quad\land\ \exists\nu:\mathcal V',\quad
\operatorname{RootAgreement}_A(\nu)\\
&\qquad\land\ R_{A,w'}(\sigma',\tau')\\
&\quad\land\ \sigma'.\mathrm{joins}=\sigma.\mathrm{joins}
\ \land\ \sigma'.\mathrm{frames}=\sigma.\mathrm{frames}\\
&\quad\land\ \tau'.\mathrm{frames}=\tau.\mathrm{frames}.
\end{aligned}`

**Reading and correspondence.** The source binds $`d` and resumes $`k`;
the target writes its corresponding local and retains the restored caller
frames. This abbreviates the exposed signature of the source-reviewed
[`rootedLet_publishes_and_resumesCaller`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1100).
Lean explicitly provides the new validated relation and its root agreement.
There is no separate final $`\operatorname{Closed}_c` conjunct in this
fourteen-step signature. Neither statement assumes intermediate paths,
future publication separation or whole-program current-step admission.

# Why fresh-region separation preserves the caller

Write $`\operatorname{ownedReach}_h(v)` for the source locations $`j` satisfying
{name Fir.LeanIR.Impure.Reachable}`Reachable` $`h\ [v]\ j`. This includes a heap
root itself and follows owned edges, as introduced in the example.

Transport from the historical caller witness into $`w_0`, followed by the
related initializer-entry heap, puts saved retained-token locations $`\ell`
below $`c`. No equality of the two entry cutoffs is assumed.
The Array root is $`c` itself, and its only element is tagged zero, which has no
owned heap edge. Allocation, the in-place push and publication maintain closure
at the original cutoff. In the notation of the
{ref "heap-caller-invariant"}[heap/caller argument],

$$`\ell<c\le j.`

Here $`j\in\operatorname{ownedReach}_{h}(\operatorname{heap}(c))`, with $`h`
the returned source heap, is distinct from the physical target result $`q`.
For the tracked set, use two partial maps, undefined outside these exact cases:

* $`\operatorname{cap}_F(x)=b` exactly when the authoritative
  {name Fir.Wasm.findReuseCapacityEvidence?}`findReuseCapacityEvidence?`
  query at $`F,x` returns a retained-at-least capacity bound $`b\in\mathbb N`.
* $`\operatorname{tok}_E(x)=\ell` exactly when source environment lookup at
  $`E,x` returns a reuse token containing source location $`\ell`.

These abbreviate the precise results `some (.retainedAtLeast b)` and
`some (.reuseToken (some ℓ))`, respectively. The identifier $`x` may be any
tracked variable, not only the let destination. $`\operatorname{cap}_F`
reports the retained-capacity evidence; it does not by itself assert an actual
heap capacity. Thus

$$`\begin{aligned}
\operatorname{Tracked}(F,E)=\{\ell\mid{}&\exists x,b,\quad
\operatorname{cap}_F(x)=b\\
&\land\ \operatorname{tok}_E(x)=\ell\}.
\end{aligned}`

For this exact tracked set, the historical facts, witness transport, entry
heap relation and region closure give

$$`\begin{aligned}
&\operatorname{Tracked}(F,E)\subseteq\{\ell\mid\ell<c\},\\
&\operatorname{ownedReach}_{h}(\operatorname{heap}(c))
\subseteq\{j\mid c\le j\},\\
&\operatorname{Tracked}(F,E)\cap
\operatorname{ownedReach}_{h}(\operatorname{heap}(c))=\varnothing.
\end{aligned}`

The disjointness is the caller-facing consequence. It is weaker than the
whole-region $`\operatorname{Closed}_c(h)` proved at publication; it does not
replace that predicate in the thirteen-step statement. Its Lean counterpart is
{name FirTalos.Concrete.ReuseTokenPublicationDisjoint}`ReuseTokenPublicationDisjoint`.

Consequently marking the returned graph persistent cannot reach the caller's
saved token locations. {bpref "fresh-publication-separation"}[] derives this
separation and transports the retained facts. Representation at the object ABI
alone would not imply it: an arbitrary older object could reach a saved token.

The current witness may evolve, while the historical caller and initializer
entry runtime/store/witness anchors remain fixed. Transport to the produced
witness is legitimate. Resetting the construction entry to the post-allocation
runtime/store/witness would move its cutoff past $`c` and invalidate the
returned-root lower bound. The proof transports the original caller facts
through the active construction scope, then consumes it to restore the caller.

# Why these invariants are needed
%%%
tag := "w6-invariant-design"
%%%

The initializer shows why the execution relation needs semantic information
about both the current computation and its saved callers. General compilation
must retain the same kinds of facts at each intermediate state:

:::table +header
*
  * Preservation question
  * Required information and destination
*
  * Does each value have the representation its next use expects?
  * Precise facts about the representation a value's producer establishes and its next use requires: {bpref "provenance-closure"}[] and the {ref "provenance-design"}[provenance account].
*
  * Can an allocation or mutation safely advance the related heap?
  * Live roots, reuse/capacity facts and finite resource guards. Fresh heap results need a construction region and publication back into the saved caller: {bpref "heap-miss-closure"}[] and the {ref "heap-caller-invariant"}[heap/caller account].
*
  * Does a call, cache lookup or external operation preserve the continuation and effects?
  * Exact argument/result ABI rows, saved frames/cache state and primitive/handler laws: {bpref "external-spec"}[], {bpref "external-admission"}[] and the {ref "admission-coverage"}[operation map].
:::

For a first program instance, prove the semantic facts from its actual code
and checked blocks, then discharge the conditional consumer's full admission
interface. These instance proofs can expose the right general invariant.
Later, {bpref "admission-closure"}[] must construct admission uniformly from
supported compilation and the maintained relation. That future result cannot
be a premise of the independent instance proof used to guide it.

The graph gives the mathematical dependencies among these obligations;
{bpref "closed-export"}[] and {bpref "resident-linking"}[] identify extensions
of the successful-return result. Prose navigation links describe the future
specialization route without making it a current proof edge. The {ref "w6-formal-catalog"}[formal catalog] expands these branches with their
checked associations and open statements.

# From one step to an executable return
%%%
tag := "w6-proof-mechanism"
%%%

The conditional proof has four stages. They explain what the invariant must
retain and where the missing compiler facts are consumed.

## 1. Establish the entry relation

Supported compilation fixes the entry/export, adapted function, hosts and
selected result kind. Cache alignment and the existing runtime/parameter
contract give $`R_{A,w_0}(\sigma_0,\tau_0)` through the checked
{bpref "rooted-entry"}[].

## 2. Match a successful source step

The proved
{name FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.advance_of_step}`advance_of_step`
has the following schematic form under uniform current-step admission and
address-space safety. The successful source transition is an explicit premise.
A control rank decreases whenever matching takes zero target steps:

$$`\begin{aligned}
&R_{A,w}(\sigma,\tau)\land(\sigma\leadsto_s\sigma')\\
&\quad\Longrightarrow\exists m,\tau',w',\quad
 \tau\overset{m}{\longrightarrow}_{M}\tau'\ \land\ R_{A,w'}(\sigma',\tau')\\
&\qquad\land\bigl(m=0\Longrightarrow
\operatorname{rank}(\sigma')<\operatorname{rank}(\sigma)\bigr).
\end{aligned}`

The guards are real hypotheses, not conclusions of validator acceptance.
The rank is {name FirTalos.Concrete.compilerStructuredControlRank}`compilerStructuredControlRank`.
A source administrative step may take zero target steps; strict rank decrease
prevents an infinite sequence of zero-target-step matches. It gives no uniform
bound on finite stuttering bursts between positive target paths. Other steps
may require several target instructions. This theorem handles successful source
advancement, not the general fault case.

## 3. Compose a finite path

Induction concatenates the derived target paths and carries the relation at
each new witness, with the same original ABI. Its observation component gives
world and ordered-trace agreement at every finite prefix. No new entry
invariant is requested at intermediate states. The proved conditional
consumer is {bpref "rooted-steps"}[].

## 4. Extract the terminal value and use adequacy

A successful source endpoint has a yielded value and an empty source
continuation. The rooted relation identifies its representation at $`A`.
Target-only administrative labels may still need unwinding: terminal extraction
and executable adequacy derive the remaining target path and exported return.
Adequacy converts the structured-machine path into an actual executable export
return in Talos.
The public conclusion is the observation-facing postcondition of
$`P_{\mathrm{success}}`, with the observation and {bpref "return-post"}[]
already stated in the successful-return guarantee. This is the checked conclusion of
{bpref "conditional-return"}[].

The internal path theorem uses the actual source endpoint runtime. The public
wrapper constructs that runtime as its existential witness; equality of the
public observations alone does not identify globals or the location cursor.
Thus the path theorem is proof evidence for the wrapper, not a reason to
silently strengthen the stated property.

Faults require a separate terminal argument. The existing certificate
consumer {bpref "conditional-fault"}[] is proved, while {bpref "fault-closure"}[]
must construct its evidence and executable trap correspondence internally.

# How the initializer proof composes its local steps

The uniform argument above uses a supplied admission law. The initializer
instead derives its paths directly from local operation laws. Its actual
composition is:

1. [`stageFreshLazyAtRoot`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L58) takes one source step and saves the validated caller/root/publication continuation; the target state is unchanged.
2. [`ConcreteStructuredFreshLazyFrame.enter`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L109) takes one source step and three target steps into the cold initializer. [`initializer_bindingKinds`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L440) derives the actual five local ABI facts from supported compilation.
3. [`literals_mkEmpty_box`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L545) supplies six body steps; [`push_stage_call_bind`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L303) supplies three more. [`body_returns`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L621) adds the return and composes their target paths. Region-indexed local/host transports derive the fresh-yield relation at the original entry; the yielded value is the initializer's local endpoint.
4. [`ConcreteStructuredFreshLazyReturned.publish`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L199) consumes that fresh yield and saved frame: one source step and seven target steps reach the rooted pre-bind outcome, preserving region closure.
5. The fourteen-step companion uses the actual source bind and target `local.set`, then reindexes the saved root agreement at the unchanged caller frame stacks.

Thus the source counts are $`1+1+10+1=13` and $`13+1=14`. Target paths are
concatenated with their actual lengths; the top-level theorems quantify the
total target count existentially. The source and target do not share a clock.
The final caller statement retains the original export ABI $`A` throughout
the local Array construction and caller restoration.

# From a selected program to the general compiler theorem
%%%
tag := "retained-example-boundary"
%%%

The initializer proof supplies source/target paths and caller preservation
from local operation laws. It does not assume the general current-step
admission law. This is the kind of semantic block that can guide an independent
proof for a selected program, while testing whether the maintained relation
contains the right information. It proves neither that the Stored export
reaches the block nor correctness of that whole export.

The selected source function is `Zip.Wasm.compressStored : ByteArray → ByteArray`.
At the immutable lean-zip nomination `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21`,
its [definition](https://github.com/kim-em/lean-zip/blob/273d0d6cd9cab77c7f3489b0b0b1f6e543315d21/Zip/Wasm/Stored.lean#L8)
calls `Zip.Spec.DeflateStoredCorrect.deflateStoredPure`. The
[source roundtrip theorem](https://github.com/kim-em/lean-zip/blob/273d0d6cd9cab77c7f3489b0b0b1f6e543315d21/Zip/Spec/DeflateStoredCorrect.lean#L751)
proves the application property $`Q_{\mathrm{stored}}`:

$$`\begin{aligned}
&\forall a,N,\quad |a|\le N\Longrightarrow\\
&\operatorname{inflateReference}(\operatorname{compressStored}(a),N)
=\operatorname{ok}(a).
\end{aligned}`

This is a theorem over arbitrary source byte arrays with the decoder's explicit
output-size bound. Its Lean 4.33 source was reviewed on 2026-10-05; no fresh
build, transitive-axiom audit or Blueprint association is claimed here.
The pinned zip-common source is `4425bab1f9522307d77e8d485bc536149ba31c36`.

FIR captures this program's actual final impure LCNF. Kernel quotation installs
[`RetainedRC2.program`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/Fir/Compiler/LCNF/retained-example/RetainedRC2.lean.in#L10),
a closed {name Fir.LeanIR.ImpureProgram}`ImpureProgram`; checked lookup/body equations identify the
real initializer. Production lowering reads back that same definition.
Constructor re-quotation and fresh-process readback establish structural capture
identity. Lean-source-to-LCNF semantic correspondence is a further bridge.
Embedded expressions remain data and unsupported metadata is rejected.
Historical oleans and diagnostic JSON remain provenance evidence; a newer
toolchain requires its recorded capture/setup identity.

The source roundtrip property $`Q_{\mathrm{stored}}` and local initializer
family $`Q_{\mathrm{init}}` have different conclusions. The first is an
application theorem in source Lean; the second is a compiler-semantic block
for the captured initializer. The open {bpref "stored-export-instance"}[]
asks for $`P_{\mathrm{success}}(p_{\mathrm{stored}})` at the captured
`Zip.Wasm.compressStored` export, universally over its allowed entries and
inputs. Closed static equations about captured code, export, ABI and supported
compilation can be computational. Primitive behavior, related ByteArray entries,
finite resources and semantic preservation still require proofs or retained
execution contracts. Validator acceptance alone does not provide them.

The current independent route constructs those semantic facts from the actual
captured program and then uses {bpref "conditional-return"}[]. Its present
admission interface is stronger than a law just about the selected entry's
reached states: it quantifies every supported function and recursively validated
current outcome of the program. The initializer block derives its own paths
and does not discharge this uniform interface. Remaining operation coverage,
producer/use-site provenance and nested heap-miss preservation must be proved
before that consumer yields a whole-export result. A direct selected-entry
proof could use a different route.

The eventual general theorem is
$`\forall p,\ H(p)\Longrightarrow P_{\mathrm{success}}(p)`.
Here $`H(p)` is production supported-export and static compilation, adaptation
and host-resolution evidence. External, resource and entry contracts still
scope the invocations in $`P_{\mathrm{success}}`; compiler-owned admission,
provenance and heap-miss preservation must be derived internally.
{bpref "validated-return"}[] is checked local assembly for that target, with
unfinished {bpref "external-spec"}[] and {bpref "admission-closure"}[].
The independent instance proof can shape those general constructions. Once
they are complete, the same fixed-program statement can instead follow by
specialization, with its input scope and retained conditions preserved.

A released-output roundtrip would additionally compose source/capture semantic
correspondence, ByteArray entry/result refinement, resident-helper refinement
and link preservation, and exact-byte encoding/release preservation. The
{ref "proof-scope"}[evidence boundaries] keep these extensions distinct from
the contracted successful-return property.

# What is proved and what remains open
%%%
tag := "w6-theorem-menu"
%%%

The first goal is successful-return correctness, written
$`P_{\mathrm{success}}(p)`. Fixing $`p` fixes a program, not an input: a program
instance must cover every related admitted entry and input. The source
application theorem and the initializer proofs above are already useful
semantic examples, but have different conclusions from the whole-export goal.

:::table +header
*
  * Claim
  * Guarantee
  * Status and retained premises
*
  * Source stored-compression roundtrip, $`Q_{\mathrm{stored}}`
  * Decoding the compressed source bytes returns the original arbitrary byte array, with an explicit decoder output-size bound.
  * Reviewed theorem source at the pinned lean-zip revision; no fresh external build or Blueprint association. See the {ref "retained-example-boundary"}[source statement].
*
  * Captured initializer family, $`Q_{\mathrm{init}}`
  * A derived target path matches thirteen source steps and fresh-region publication; the fourteen-step companion restores the rooted validated caller.
  * Genuine local semantic proofs cited as reviewed source evidence. Primitive/handler laws, related callers, cold cache and finite headroom remain inputs; neither theorem proves the whole export. The {ref "worked-retained-initializer"}[worked proof] follows the actual states and lemma composition.
*
  * {bpref "rooted-steps"}[] and {bpref "conditional-return"}[]
  * Every finite source prefix has a matching target path; a successful source evaluation yields an actual export return with the selected ABI and exact observation.
  * Proved conditional theorems. Uniform compiler admission, address-space safety and the existing entry/cache/arity conditions are supplied.
*
  * {bpref "stored-export-instance"}[]
  * $`P_{\mathrm{success}}(p_{\mathrm{stored}})` for the selected captured program, universally over its allowed inputs.
  * Open. First construct this program's semantic facts and use the proved conditional consumer; the unfinished general theorem is not a prerequisite.
*
  * {bpref "validated-return"}[]
  * Eventually, $`\forall p,\ H(p)\Longrightarrow P_{\mathrm{success}}(p)` for supported compiled exports.
  * Local composition is checked, but the external specification and admission construction are explicit holes. $`H` is static supported-export/compilation evidence; compiler-owned admission must be derived.
*
  * Faults, closed exports and resident linking
  * {bpref "conditional-fault"}[] proves a refined executable trap from a supplied certificate. {bpref "closed-export"}[] would combine prefixes, returns and faults; {bpref "resident-linking"}[] adds installed implementations.
  * The certificate consumer is proved; general fault construction and both extensions are open. Linking and released-byte correctness require their own bridges.
:::
