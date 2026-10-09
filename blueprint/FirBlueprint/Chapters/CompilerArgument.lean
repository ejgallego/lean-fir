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

When a Lean program is compiled to Wasm, its values become machine words and
its objects become regions of linear memory. The two executions therefore look
different. We want to prove that they still do the same computation: whenever
the source returns, the compiled export returns a representation of the same
value and preserves the observable effects of external operations, in order.
Following a call that constructs and returns a small Array will show why this
requires a relation between whole machine states, as well as between values.

We are building this argument first for selected programs, using their actual
compiled code and the semantic behavior of their operations. A theorem about
one such program must apply to every allowed input and entry state. These
instance proofs can reveal what a general compiler proof needs to remember.
Later, a general theorem could establish the same instance statements by
specialization. For now, we have proved some local blocks and conditional
execution theorems; the whole-program guarantees remain goals.

# A call that must return to its caller

Our example is an initializer in a captured Lean program. It takes no arguments,
creates an Array with capacity five, pushes tagged zero into it, and returns
the resulting singleton. Its caller is paused at a let binding: it needs the
Array in order to bind the destination variable and continue. During the call,
the machine must remember both the caller's variables and where its execution
should resume.

The initializer is lazy. Its result is stored in a global cache, so later calls
can reuse it. We consider a cold cache, where the result is absent and the body
runs. Returning from that body is only part of the operation. The runtime must
also publish the Array in the cache and mark its owned heap graph persistent,
protecting those cells from ordinary reuse, before it resumes the source caller.

Publication creates the main proof problem. The suspended caller may hold a
reuse token for an older heap cell, together with facts that allow it to reuse
that cell later. Those facts require the cell to remain ordinary, or
nonpersistent. The initializer must therefore return an Array whose publication
preserves them. We will prove this by separating the freshly constructed graph
from the caller's tracked cells. The local theorem applies to any supported
caller satisfying its assumptions; correctness of the selected compression
export, including whether it reaches this block, is a further question.

# The source program and the two machines
%%%
tag := "w6-machines"
%%%

The source program $`p` is written in Lean's final intermediate representation,
impure LCNF. At this stage, operations such as allocation, reference counting,
mutation and object access are explicit. FIR gives this language a machine
semantics. The compiler theorem compares this captured final-LCNF execution
with Wasm; relating the original Lean program to that capture is an additional
proof. In the example, the source machine evaluates the initializer's
operations, saves the caller during the call, and eventually resumes its
continuation.

Write $`\sigma` for a source state. It records the current code, the environment
of local variables, local join points, saved continuation frames and runtime
$`r`. The runtime holds the source heap and global cache, as well as the state
and history of external operations. An environment maps variables to semantic
values; a continuation frame records work to do after the current computation
returns. Source heap references name locations rather than concrete addresses.

A source step either advances to another state, reports a return, or reports a
semantic fault. For successful advancement, write
$`\sigma\leadsto_s\sigma'`; write $`\sigma\overset{n}{\leadsto}_s\sigma'` for
exactly $`n` such steps. The source external implementation $`\varepsilon` is
fixed during an argument. It specifies the semantic response to calls such as
`Array.mkEmpty` and `Array.push`. These arrows describe FIR's
{name Fir.LeanIR.Impure.executeStep}`executeStep` and
{name Fir.LeanIR.Impure.ExecSteps}`ExecSteps`.

## The target package, export and result ABI

Compilation produces a Wasm module and selects an export $`e` corresponding to
the source entry. The target execution also needs implementations of imported
operations. Write $`M` for the compiled package: the compiler's symbolic module,
the Wasm module produced by its adapter, and the resolved host environment.
The host functions are required to satisfy the operation contracts used in the
proof. This is the contracted execution boundary; connecting it to a module
with resident implementations and to released bytes will require further
proofs.

Write $`\tau` for a target state and $`S` for its store. The store contains
concrete memory, while target locals and the operand stack contain physical
Wasm values. Target frames record how execution returns through calls, blocks
and loops. The structured target machine exposes this control flow and uses
Talos to execute the individual instructions and imported calls. Its finite
paths are written $`\tau\overset{m}{\longrightarrow}_M\tau'`, with $`m` target
steps. They are defined by
{name FirTalos.Correctness.StructuredWasmStep}`StructuredWasmStep`.

A compiler proof must allow different step counts. The source can finish a
binding in one step while the target needs several instructions to obtain and
store its representation. Conversely, saving a source continuation may require
no target instruction. We will relate the states reached by these unequal
paths, rather than ask the two machines to advance in lockstep.

The export fixes how its final result is represented. This is its result
application binary interface (ABI) kind, which we denote by $`A`. A nested
initializer can return an object even when the enclosing export returns a
scalar. The relation must remember the export's original $`A` while these
nested calls run, so that the final return has the representation the export
promised. The successful-return argument begins with a finite source evaluation;
it derives a target execution from that evaluation. Source totality is a
separate property, and interpreter fuel is only a limit on an executable runner.

# Observations and the representation carried through a call
%%%
tag := "w6-rooted-relation"
%%%

Suppose a source variable refers to an Array at heap location $`\ell`. Its
compiled local contains a Wasm word $`q`, and the Array occupies a concrete
memory region beginning at byte address $`a`. Correctness must explain how
$`q` and that memory represent the source Array. A refinement witness $`w`
records this correspondence for source values and live heap objects. At a
related state, it also relates the global cache, the state of external
operations and their ordered trace.

The invariant requires each witness to be valid. In particular, distinct source
locations visible through its mapping have distinct represented addresses.
When allocation or return changes the states, the proof may produce a new
witness. Each new witness has its own validity proof; the argument does not
require every phase to use the entry witness or an extra uniform extension
law between all witnesses.

Representation alone is insufficient during a call. The two machines must
also agree on what computation is running and what will happen when it returns.
Write $`R_{A,w}(\sigma,\tau)` for this full execution relation. It combines
value and runtime representation with validated current code, generated
continuations, cache agreement and the facts saved for callers. The index $`A`
remembers the original export's result kind. The active callee retains the
representation facts appropriate to its own result, which may have a different
kind. Hiding the witness gives the relation

$$`R_A(\sigma,\tau)\quad\Longleftrightarrow\quad
\exists w,\ R_{A,w}(\sigma,\tau).`

The initial relation is obtained from the correspondence between source entry
data and encoded target parameters. Carrying the saved caller facts through construction lets publication
re-establish this relation. The proof can then move from a locally represented
Array back to a validated caller, and finally to the representation promised
by the export.

At the end of a source execution, the public observation $`o` consists of its
outcome, heap, world and ordered external trace. The world records the observable
state of external operations; the trace records their names, arguments and
results in order. Write $`O(r,v)` for the returned observation built from
runtime $`r` and value $`v`. Globals and the fresh-location cursor are parts of
$`r`'s runtime state, but are absent from this public observation. Thus an
observation describes more than a returned value, while identifying less than
an entire runtime.

The relation $`R_{A,w}` abbreviates
{name FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt}`ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt`.
Its witness-hiding form is used by the conversion
{name FirTalos.Concrete.ConcreteStructuredCompilerCurrentStepAdmission.toRootedTraceSimulation}`toRootedTraceSimulation`.
These links identify the Lean relations underlying the mathematical notation.

# The precise successful-return guarantee
%%%
tag := "w6-notation"
%%%

Choose a supported source program $`p`, its compiled package $`M`, export $`e`
and the export's result ABI $`A`. These choices fix the code and representation
convention. They leave the input and the related entry states arbitrary. Also
fix the source external implementation $`\varepsilon`, subject to the operation
contracts used below.

An invocation starts with source runtime $`r_0` and environment $`E_0`, concrete
target store $`S_0`, a row $`\bar u` of encoded Wasm parameters, and an initial
refinement witness $`w_0`. It includes the caller's retained reuse facts and a
finite byte budget. The allowed invocations satisfy four conditions:

* The source primitive laws and installed implementation contracts cover the
  operations in the argument. Finite resource bounds and address-space safety
  hold for the execution.
* The compilation context and source program have the same cached declarations.
* The encoded parameter row has the selected target function's parameter count.
* The source runtime and environment are related to the target store and
  parameter-derived locals, including the required cache, reuse, capacity and
  closure-ABI facts.

Let $`\sigma_0` be the source entry state for such an invocation. Write
$`\sigma_0\Downarrow_{\varepsilon}(o,v)` when its finite source evaluation has
observation $`o` and returned value $`v`. This abbreviates
{name Fir.LeanIR.Impure.ExecEvaluates}`ExecEvaluates` with returned outcome.
For the target, write
$`\operatorname{Return}_{M,e}(S_0,\bar u;r,v,A)` when the export actually
terminates from $`S_0,\bar u` with the refined return postcondition for runtime
$`r`, value $`v` and ABI $`A`. That postcondition supplies one terminal witness
and physical result. It relates the live runtime and result, clears the target
failure channel, and leaves the represented result as the single returned
operand with an empty caller tail.

Successful-return correctness is the following requirement for every allowed
invocation:

$$`\begin{aligned}
&\forall o,v,\quad \sigma_0\Downarrow_{\varepsilon}(o,v)\\
&\quad\Longrightarrow\exists r,\quad
 o=O(r,v)\ \land\ \operatorname{Return}_{M,e}(S_0,\bar u;r,v,A).
\end{aligned}`

We denote the program property by $`P_{\mathrm{success}}(p)`. It says that every
finite successful source computation from an allowed input forces an actual
export return with the same observation and the fixed result ABI. Fixing $`p`
fixes a program, not its input. Source termination for all inputs would be a
further theorem.

The existential runtime $`r` is part of the public statement. In the proved
conditional argument, it is chosen to be the actual final runtime of the source
execution. Observation equality by itself does not force that choice, because
it omits globals and the location cursor. Keeping this distinction preserves
the precise public guarantee while explaining how the proof establishes it.

The entry conditions supply related starting data and the independent operation
and resource contracts. The compiler proof must establish the semantic facts
needed at later states. The current conditional theorem does this from a supplied
*current-step admission* law: at every supported validated operation, the
argument/result representations, operation behavior and resource accounting
required by the step proof are available. Constructing that law from the actual
compiled code and the maintained invariant is one of the open compiler
obligations. Static validator acceptance supplies syntactic facts and does not
alone establish those semantic properties.

In Lean, $`A` is `spec.sourceResultKind`. The related-entry condition is
{name FirTalos.Concrete.ConcreteReuseCapacityCacheAbiFrame}`ConcreteReuseCapacityCacheAbiFrame`;
the target return predicate is
{name FirTalos.Concrete.ConcreteExportTerminatesWith}`ConcreteExportTerminatesWith`
with {bpref "return-post"}[] and an empty operand tail. Its module and host
arguments are `adaptedModule.wasmModule` and `hosts.env`. The retained
{name FirTalos.Concrete.ConcreteStructuredCurrentStepAddressSpaceSafety}`ConcreteStructuredCurrentStepAddressSpaceSafety`
law checks admitted steps against each frame's current remaining budget.
The conditional result
is {bpref "conditional-return"}[]. The mathematical property above preserves
that result's public observation-facing shape.

# Follow the initializer through its actual states
%%%
tag := "worked-retained-initializer"
%%%

Let the caller's let destination be $`d` and the remaining code be $`k`. When
the call begins, the source saves its environment $`E`, join points $`J` and
continuation frames $`F_s`. The target has its own saved frame stack $`F_t`;
its local $`i` corresponds to source variable $`d`. Saving these components
lets each machine resume the same caller after the initializer returns.

The caller's invariant was established at a historical entry with runtime,
store and witness $`(r_h,S_h,w_h)`. The initializer begins later, at the current
$`(r_0,S_0,w_0)`. Its fresh region starts at the source heap cursor of $`r_0`,
which we call $`c`. This is the value of `r₀.nextLocation`. The proof keeps this
entry and cutoff throughout construction, even as the current runtime and
witness change. They provide the fixed reference point for the freshness
argument.

The newly allocated Array occupies source location $`c`. Write
$`\operatorname{heap}(c)` for the source value referring to that location.
Its only element will be tagged zero, an immediate value with no owned heap
edge. An owned edge is a heap-reference field whose ownership the parent
retains; owned reachability follows those fields from a root. Thus the Array
has no older child that publication could reach. The proof will also preserve
closure of the whole fresh region, meaning that every owned edge from a parent
at or above $`c` stays at or above $`c`.

Let $`B` be the available concrete byte budget and $`\Delta` the allocation
cost of an Array with five slots. The following execution uses that allocation
once. Boxing the zero and pushing it into the empty Array require no additional
physical allocation. Assuming the related caller, cold cache, operation laws
and $`\Delta\le B`, the proof follows these states:

:::table +header
*
  * Source step count
  * Source computation
  * Target computation
*
  * 0: caller
  * The caller is at the let binding of the initializer to $`d`.
  * Generated lazy-call code and locals represent that caller; the export result kind is $`A`.
*
  * 2: callee entry
  * Staging saves the caller, then the cold initializer begins with an empty local environment. Cache and bind frames sit above $`F_s`.
  * The call and label continuation have been entered in three target steps. Construction is anchored at $`(r_0,S_0,w_0)`.
*
  * 8: allocation and boxing
  * Six body steps evaluate the literals, call and bind the empty Array, and box tagged zero. The Array is at $`c` with capacity five.
  * Allocation produces a witness mapping $`c` to a byte address $`a`; a word $`z` represents tagged zero.
*
  * 12: local return
  * Three push steps and one return finish the ten-step body. The Array contains one tagged zero, with cache and bind frames still pending.
  * The push stores $`z` in place. A physical result $`q` represents the Array under the produced witness and original construction scope.
*
  * 13: publication
  * The runtime caches $`\operatorname{heap}(c)` and marks the returned graph persistent. The destination bind is still pending.
  * Seven target steps publish and reload the result. Caller locals and frames are already restored; the destination `local.set` remains pending.
*
  * 14: caller resumption
  * The bind installs the Array at $`d` and resumes $`k`, with the original joins and caller frames.
  * One `local.set` writes the corresponding target local. The caller's remaining budget is $`B-\Delta` and only $`d`'s old reuse fact is erased.
:::

The source runtime changes in two distinct ways. `Array.mkEmpty` and
`Array.push` append their arguments and results to the external trace, in that
order, while preserving the world. Publication then updates the cache and
persistence metadata; the destination bind updates the environment. Tracking
these changes separately lets the relation account for both effects and caller
restoration. The initializer's local return still has a continuation to run;
only the enclosing export's final return completes the successful evaluation.

## Source and target at four proof checkpoints

The panels show the symbolic states obtained by this proof family. A drawn
token $`\ell` represents any tracked caller token, when one exists. Source
locations and target byte addresses have separate axes. In each phase,
$`q` represents the returned Array and $`z` its tagged element; the subscript
identifies the checkpoint. The witnesses and addresses are derived at those
checkpoints, while both entry anchors, $`c` and the export ABI $`A` stay fixed.

At **step 2**, the machines have saved the cache and bind continuations and
entered the callee. The target entry segment has three steps. The fresh Array
has not yet been allocated.

```diagram
FirBlueprint.RetainedInitializerScene.entered
```

At **step 12**, the ten source body steps have produced the singleton and its
represented target result. The body has a finite target path, whose length
$`T` the proof derives. The local-return relation still remembers the original
construction region and the suspended caller.

```diagram
FirBlueprint.RetainedInitializerScene.returned
```

At **step 13**, publication has restored the target caller's locals and frames
and reloaded the Array result. The source still has the callee environment and
joins, followed by the bind frame carrying $`d,k,E,J`. This asymmetry is why
publication and caller resumption have separate statements. The relation at
$`A` and fresh-region closure hold at this checkpoint.

```diagram
FirBlueprint.RetainedInitializerScene.published
```

At **step 14**, the source installs $`\operatorname{heap}(c)` at $`d` and
restores the caller's joins and frames. The target writes local $`i` and keeps
its already restored frames. We now have a validated caller ready to continue.

```diagram
FirBlueprint.RetainedInitializerScene.resumed
```

# The common assumptions of the two local theorems

These are families of executions of the same captured initializer,
`RetainedRC2.initializer` in `RetainedRC2.program`. The compiled package $`M`,
source external implementation $`\varepsilon` and original export ABI $`A`
are fixed. The supported caller is arbitrary: its function and compilation
context, active result kind, expected result, labels, historical entry,
current states, environment, target locals and code may vary. So may its reuse
facts $`F`, budget $`B`, let destination $`d` and continuation $`k`.

The first assumption is a related, validated caller at precisely this let
binding. Its source let value is the initializer applied to no arguments.
The relation connects the actual caller function to its compiled and adapted
code, accounts for the saved frames, and carries agreement with the original
root result kind $`A`. The active-result equality is retained even though the
initializer itself returns an object. The cache is cold: the initializer's
entry is absent from the source globals.

Next come the operation laws. The source contract specifies empty-Array
allocation and pushing a tagged element into a fresh empty receiver with spare
capacity. Its uniform laws are specialized here to capacity five and payload
zero. The concrete host must implement those operations at the representations
that the proof encounters. For allocation, its empty handler must satisfy the
handler equation at $`S_0,w_0` for every related capacity-five request. For push,
the law ranges over every concrete runtime and witness related to the source runtime after
empty allocation, every mapped address of $`c`, every word representing tagged
zero, and every request with the exact `Array.push` name and arguments. It then
provides the in-place handler equation. This quantification is needed because
the allocation proof produces a representation; the push must work at whichever
related representation is produced.

Finally, the concrete allocation must fit: $`\Delta\le B`. This is a physical
resource assumption, since the source semantic heap is unbounded. The code
uses no further allocation in boxing or in this push branch, so the remaining
budget is $`B-\Delta`.

These assumptions describe the starting caller and operation behavior. The
proof derives the source execution, target paths, callee support, generated
cache and continuation facts, the five local binding-kind facts, and the
post-body construction scope. A general current-step admission law is not a
premise of this local derivation.

The caller relation is
{name FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome}`ConcreteStructuredValidatedCodeOutcome`;
its root agreement is
{name FirTalos.Concrete.ConcreteStructuredValidationAgreesAtRoot}`ConcreteStructuredValidationAgreesAtRoot`.
The source operation laws form `FreshArrayExternalContract`, and $`\Delta`
is {InlineLean.lean}`Fir.Wasm.Concrete.residentArrayAllocationBytes 5`.
The concrete handler laws concern the installed host, whose replacement by
resident code requires its own implementation refinement.

# Publication and caller resumption are separate conclusions

We can now state what the two theorems prove. In both, the assumptions above
range over every supported caller and related initial pair
$`\sigma_0,\tau_0`. Here these are the caller states at the initializer let,
before staging, rather than the enclosing export's entry states. The statements derive the execution from those starting
data. The source path lengths are exact; the target lengths, intermediate
states and final witnesses are obtained by the proof.

## Publication after thirteen source steps

Write $`h(\sigma)` for the source heap in state $`\sigma` and
$`\operatorname{Closed}_c(h)` for closure of the whole region at or above $`c`:
every owned edge from a parent in that region has its child there too. The
publication theorem gives

$$`\begin{aligned}
&\exists m,\sigma_{13},\tau_{13},w_{13},\quad
  \sigma_0\overset{13}{\leadsto}_s\sigma_{13}\\
&\quad\land\ \tau_0\overset{m}{\longrightarrow}_M\tau_{13}\\
&\quad\land\ R_{A,w_{13}}(\sigma_{13},\tau_{13})\\
&\quad\land\ \operatorname{Closed}_c(h(\sigma_{13})).
\end{aligned}`

The relation says that publication has re-established the execution invariant
at the export's original result kind. Region closure supplies the heap
separation used to protect the suspended caller. Together these are enough to
continue the compiler argument beyond local Array construction.

The constructed endpoint also identifies the cached value as
$`\operatorname{heap}(c)`. Its source bind is still pending, while the target
has already restored caller locals and frames and has its destination
`local.set` left to execute. These descriptions follow from the endpoint built
in the proof. The displayed public conclusion consists of the paths, rooted
relation and whole-region closure.

## Caller resumption after fourteen source steps

One more source bind and one target local write complete the return to the
caller. Under the same assumptions, the companion theorem provides

$$`\begin{aligned}
&\exists m,\sigma_{14},\tau_{14},w_{14},\quad
  \sigma_0\overset{14}{\leadsto}_s\sigma_{14}\\
&\quad\land\ \tau_0\overset{m}{\longrightarrow}_M\tau_{14}\\
&\quad\land\ R_{A,w_{14}}(\sigma_{14},\tau_{14}).
\end{aligned}`

It also restores a validated caller with the following state. Let $`r_{\mathrm{pub}}`
be the runtime after `Array.push`, with the initializer global set to
$`\operatorname{heap}(c)`. This is its source runtime. The caller's environment is
$`E[d\mapsto\operatorname{heap}(c)]`, its current code is $`k`, its budget is
$`B-\Delta`, and its reuse facts are $`F` with only the old fact for $`d` erased.
The source joins and continuation frames are exactly the initial caller's
$`J,F_s`, and the target frame stack is exactly $`F_t`. The historical entry,
caller context and function, labels, active ABI and expected result are retained.
The proof supplies a new validated-code relation for these updated indices and
agreement at the original root ABI $`A`.

This additional conclusion is what lets the caller's next operation use its
restored invariant. The fourteen-step statement exposes caller validation and
frame restoration; it has no separate final region-closure conjunct. The
thirteen-step theorem is the statement that explicitly preserves that closure.

The two results are
[`rootedLet_publishesAtBind`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1016)
and
[`rootedLet_publishes_and_resumesCaller`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1100).
The closure predicate is
{name FirTalos.Concrete.HeapRegionClosed}`HeapRegionClosed`; the erased fact uses
{name Fir.Wasm.eraseReuseCapacityFact}`eraseReuseCapacityFact`.
The cited accepted sources at `f6850d79f` provide the local theorem evidence
here; this chapter adds no association or fresh
initializer proof build.

# Why fresh-region separation preserves the caller

When the initializer returns, publication marks the returned Array and its
owned graph persistent. The suspended caller may still hold a reuse token for
an older cell. Its saved facts require that cell to remain ordinary, so the
cell must be outside the graph being marked. Fresh allocation gives us a way
to establish this separation.

Recall that $`c` is the source heap cursor at initializer entry. The saved
token's representation can be transported from the historical caller witness
to the initializer-entry witness $`w_0`. The related entry heap at $`r_0`
then places its source location
$`\ell` below $`c`. At entry, all existing source heap cells lie below $`c`, so the region at or
above $`c` is empty. The initializer allocates its Array at $`c`, and its only
stored element is tagged zero. This element has no heap reference to follow.
The local operation proofs establish and preserve whole-region closure at
the original cutoff: every owned edge from a parent at or above $`c` stays in
that region. Allocation and the in-place push preserve this edge condition. Starting at the returned root, every location $`j` reached through
owned edges is at or above $`c`. Thus a tracked cell and a location in the
returned graph satisfy

$$`\ell<c\le j.`

To state the consequence for all of the caller's tokens, let $`\mathcal T(F,E)`
be its tracked source locations. A location belongs to this set when some
variable in environment $`E` contains a reuse token naming it and that variable
has a retained-capacity fact in $`F`. Let $`\operatorname{ownedReach}_h(v)` be
the locations reached from value $`v` in source heap $`h` by following owned
heap-reference fields, including the root itself. Sharing and cycles are
allowed; immediate tagged data contributes no edge. For the publication heap
$`h`, the proof gives

$$`\begin{aligned}
\mathcal T(F,E)&\subseteq\{\ell\mid\ell<c\},\\
\operatorname{ownedReach}_h(\operatorname{heap}(c))
&\subseteq\{j\mid c\le j\},\\
\mathcal T(F,E)\cap\operatorname{ownedReach}_h(\operatorname{heap}(c))
&=\varnothing.
\end{aligned}`

Publication can therefore make the fresh graph persistent without changing the
persistence of any tracked cell. This is the fact needed to carry the caller's
ordinary-token facts through the operation. Together with representation and
capacity transport, it lets the proof restore the caller's retained facts.

The heap argument maintains a stronger property than disjointness of these two
sets. The whole region above $`c` is closed: an owned edge from any parent in
that region has its child in the same region. From this edge condition, an
induction along an owned path proves the second inclusion. The thirteen-step
publication theorem preserves this whole-region closure. Disjointness is its
caller-facing consequence.

Keeping the original cutoff is essential. If we replaced $`c` with the cursor
after allocation, the returned root would lie below the new cutoff. We would
lose the bound that separates its graph from the caller's tracked cells. The
current witness may evolve as the target allocates and returns, but the saved
caller anchor and initializer-entry anchor stay fixed throughout the argument.
This allows each new representation to be related back to the same separation
claim.

## The exact tracked set in Lean

The tracked set uses two partial lookups. Write $`\operatorname{cap}_F(x)=b`
when {name Fir.Wasm.findReuseCapacityEvidence?}`findReuseCapacityEvidence?`
returns `some (.retainedAtLeast b)` for variable $`x`; write
$`\operatorname{tok}_E(x)=\ell` when environment lookup returns
`some (.reuseToken (some ℓ))`. Then

$$`\begin{aligned}
\mathcal T(F,E)=\{\ell\mid{}&\exists x,b,\quad\operatorname{cap}_F(x)=b\\
&\land\ \operatorname{tok}_E(x)=\ell\}.
\end{aligned}`

The capacity lookup supplies evidence about a tracked variable; the related-state invariant
certifies that the corresponding concrete allocation has the required room. The reachability set
is {name Fir.LeanIR.Impure.Reachable}`Reachable` from the singleton root list.
{name FirTalos.Concrete.ReuseTokenPublicationDisjoint}`ReuseTokenPublicationDisjoint`
is the disjointness predicate, and {bpref "fresh-publication-separation"}[]
provides the separation and caller transport used here. The
{ref "heap-caller-invariant"}[heap and caller chapter] develops these relations
for general fresh constructions.

# Why these invariants are needed
%%%
tag := "w6-invariant-design"
%%%

The initializer shows why a compiler invariant has to connect the running
computation to the callers waiting behind it. Allocating a correctly represented
Array is one obligation. Returning it while preserving the caller's reuse
facts is another. The invariant provides the information needed for both,
so that each operation can leave behind a state in which the next operation
is justified.

Representation facts must be precise enough for a value's next use. A producer
can establish one encoding while a later projection, call or return requires
another property of that encoding. The compiler proof has to connect them.
This is the purpose of {bpref "provenance-closure"}[] and the
{ref "provenance-design"}[provenance argument]: they track where the needed
semantic facts come from and why they survive between production and use.

Heap operations add lifetime and resource questions. A mutation needs live
roots and appropriate ownership; reuse needs a valid retained cell and enough
physical room. An allocation needs a finite budget. The fresh initializer
also needs a construction region in which it can build a result before
publishing it to the caller. The {ref "heap-caller-invariant"}[heap and caller
argument] develops this mechanism, while {bpref "heap-miss-closure"}[] identifies
the general lazy-call obligation it must discharge.

Calls and external operations bring these facts together. Arguments and results
must have the encodings expected at their boundaries, saved frames and caches
must be restored appropriately, and external effects must obey their source
and implementation laws. The {ref "admission-coverage"}[operation map] organizes
these cases. A complete proof must derive the relevant facts from supported
compilation and preserve them through execution; the
{ref "w6-formal-catalog"}[formal catalog] records the associated results and
remaining obligations.

# From one step to an executable return
%%%
tag := "w6-proof-mechanism"
%%%

The general execution argument builds a target path by following a given
finite source computation. Its central lemma says that a successful source
step from related states has a matching finite target segment, after which
the states are related again. Once that lemma applies at every intermediate
state, induction can carry the relation all the way to a return.

## 1. Establish the entry relation

Supported compilation identifies the source entry, selected export, adapted
function, host environment and result kind. The entry data relate encoded
parameters to the source environment and runtime, and the cache-alignment
condition identifies the globals used by the compiled code. These facts give
$`R_{A,w_0}(\sigma_0,\tau_0)` through {bpref "rooted-entry"}[]. The execution
proof therefore starts with the actual compiled entry, rather than a supplied
simulation of its future behavior.

## 2. Match a successful source step

Consider a source step $`\sigma\leadsto_s\sigma'` from a state related to
$`\tau`. The current-step admission law supplies the semantic facts for the
operation at this validated code point. A separate address-space law ensures
that its admitted resource cost fits the current frame's remaining budget.
Under these laws, the step theorem derives

$$`\begin{aligned}
&R_{A,w}(\sigma,\tau)\ \land\ \sigma\leadsto_s\sigma'\\
&\quad\Longrightarrow\exists m,\tau',w',\quad
 \tau\overset{m}{\longrightarrow}_M\tau'
 \ \land\ R_{A,w'}(\sigma',\tau').
\end{aligned}`

The segment length $`m` can be zero. For example, a source administrative
transition can change its continuation without executing a Wasm instruction.
The theorem controls such stuttering with a natural-valued control rank
$`\kappa`: when the derived match takes zero target steps,

$$`m=0\quad\Longrightarrow\quad\kappa(\sigma')<\kappa(\sigma).`

Strict decrease prevents an infinite consecutive sequence of zero-step matches.
Other source steps may require several target instructions. The rank gives no
uniform bound on the lengths of finite stuttering bursts, and neither machine
uses the other's step count as its fuel.

The matching lemma is
{name FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.advance_of_step}`advance_of_step`;
$`\kappa` is {name FirTalos.Concrete.compilerStructuredControlRank}`compilerStructuredControlRank`.
Its source-step premise and its two uniform laws are essential. Validator
acceptance alone does not establish these semantic and resource facts.

## 3. Compose a finite path

Now follow a finite source path. Apply the matching lemma to its first step,
then to its second step using the relation just produced, and continue by
induction. Concatenating the target segments gives one target path. At each
checkpoint, the new witness relates the new states while the original export
kind $`A` stays fixed.

This is why preservation matters: an intermediate state need not satisfy a
new entry assumption. It satisfies the invariant carried from the preceding
step. The runtime part of that invariant preserves the world and ordered
external trace along each finite prefix. {bpref "rooted-steps"}[] is the
conditional finite-path theorem obtained by this composition.

## 4. Extract the terminal value and use adequacy

A successful source evaluation ends with a yielded value and no source
continuation left to run. The rooted relation then supplies the result's
representation at $`A`. The target may still have administrative labels to
unwind, so terminal extraction derives the remaining target steps needed to
return through them.

Finally, adequacy connects that structured-machine path to executable Talos
termination of the selected export. We have now derived the target execution,
its result representation and its observation from the source evaluation.
This gives the successful-return property through {bpref "conditional-return"}[],
with the existential runtime described in its statement. The path proof chooses
the actual final source runtime to witness that conclusion.

A source fault requires a different terminal argument. The proved
{bpref "conditional-fault"}[] uses a supplied fault certificate to obtain a
refined executable trap. {bpref "fault-closure"}[] must construct that evidence
for general compiler execution; the {ref "fault-safety"}[fault and safety
account] explains the additional boundary.

# How the initializer proof composes its local steps

The uniform argument above takes a current-step admission law as an input.
For the initializer, the proof instead follows the actual code and derives
each segment from local operation laws. This gives a concrete instance of the
same preservation idea without using general admission as a premise.

First the source stages the lazy call. It saves the validated caller and the
continuations needed to cache and bind the result. This is one source step and
no target step: the target is already at the generated lazy-call code. Entering
the cold initializer then takes one source step and three target steps. The
compilation facts identify the five local binding kinds in this actual body,
so subsequent operations use the ABI information they need.

The body begins by evaluating its literals, allocating an empty Array and
boxing zero. These take six source steps. The empty handler law supplies the
target allocation, after which the produced witness represents the source Array
at $`c`. The next three source steps stage, call and bind the in-place push.
The push handler law works at the representation produced by allocation and
stores tagged zero without allocating a second block. One return step completes
the ten-step body. The local proofs compose the corresponding target segments
and retain the fresh-region invariant at the original initializer entry.

Publication consumes that local return and the saved lazy-call frame. It takes
one source step and seven target steps, re-establishing the rooted relation and
preserving region closure. The target caller's frames have now been restored,
while the source bind remains pending. The companion proof executes that bind
and the target's destination `local.set`, then restores validation of the caller
under the updated environment, cache, facts and budget. The source counts are
therefore

$$`1+1+10+1=13,\qquad 13+1=14.`

The target paths are concatenated with their derived lengths; their total count
is existential in each theorem. The construction retains $`A` from the original
export throughout entry, Array return, publication and caller resumption.

The source composition uses
[`stageFreshLazyAtRoot`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L58)
and
[`enter`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L109)
for staging and entry;
[`initializer_bindingKinds`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L440)
derives the local ABI facts.
[`literals_mkEmpty_box`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L545),
[`push_stage_call_bind`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L303)
and
[`body_returns`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L621)
compose the body;
[`publish`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L199)
returns it to the rooted caller. These references identify the proof steps
behind the execution just described.

# From a selected program to the general compiler theorem
%%%
tag := "retained-example-boundary"
%%%

The initializer proof demonstrates that the execution relation can support a
real construction and return to an arbitrary related caller. We want to extend
this kind of reasoning across a selected program's actual code. Such a proof
would establish compiler correctness for that program on every allowed input,
while revealing which operation and preservation lemmas the general theorem
will need.

The selected application is stored compression. The Lean function
`Zip.Wasm.compressStored : ByteArray → ByteArray` produces DEFLATE stored
blocks using `Zip.Spec.DeflateStoredCorrect.deflateStoredPure`. There is already
a source roundtrip theorem: if $`\beta` is an arbitrary byte array and $`N`
is the decoder's output-size limit, then

$$`\begin{aligned}
&\forall\beta,N,\quad |\beta|\le N\Longrightarrow\\
&\operatorname{inflateReference}(\operatorname{compressStored}(\beta),N)
=\operatorname{ok}(\beta).
\end{aligned}`

Call this application property $`Q_{\mathrm{stored}}`. It says what the source
compression algorithm does. To obtain the corresponding statement for compiled
execution, we also need the compiler property
$`P_{\mathrm{success}}(p_{\mathrm{stored}})` for the captured final-LCNF program.
The initializer supplies a local family of compiler-semantic results,
$`Q_{\mathrm{init}}`, but it does not establish the whole-export property or
prove that the selected export reaches that block.

FIR's capture installs `RetainedRC2.program` as a closed impure program.
Checked lookup and body equations identify the initializer, and production
lowering reads back that same definition. Constructor re-quotation and
fresh-process readback establish structural identity of the capture. Relating
the original Lean source semantics to the captured program remains an
additional bridge. The capture's embedded expressions are data, unsupported
metadata is rejected, and its setup identity must be recorded when the toolchain
changes.

The present plan for {bpref "stored-export-instance"}[] constructs the semantic
facts needed by {bpref "conditional-return"}[] from this actual program and
its local proofs. The consumer's admission interface quantifies every supported
function and recursively validated current outcome of the program. This is
stronger than a law only about the selected entry's reached states, and the
local initializer proof is not a proof of that uniform law. The remaining code
needs operation coverage, producer/use-site representation facts and preservation
through nested heap misses. A direct proof for the selected entry could use a
different simulation route.

The same obligations appear in the intended general theorem,

$$`\forall p,\quad H(p)\Longrightarrow P_{\mathrm{success}}(p).`

Here $`H(p)` records supported-export and static compilation, adaptation and
host-resolution evidence. The external, resource and entry contracts continue
to define the allowed invocations in $`P_{\mathrm{success}}`. The general proof
must derive compiler-owned admission and preserve the representation and heap
facts internally. {bpref "validated-return"}[] provides checked local assembly
for this argument, while {bpref "external-spec"}[] and
{bpref "admission-closure"}[] remain unfinished.

The independent instance proof can guide those general constructions. When the
general theorem is available, the same fixed-program statement could instead
follow by specialization and discharge of its premises. Its input scope and
retained conditions would be unchanged. Computational checks can establish
closed equations about the code, export and successful compilation; semantic
behavior, related ByteArray entry data and finite resources still need their
own proofs or stated execution contracts.

A released-byte roundtrip goes further. It would compose the source roundtrip
with source-to-capture correspondence, the compiler instance and ByteArray
entry/result refinement, resident-helper and semantic-link refinement, and
encoding/release preservation for the exact artifact. The
{ref "proof-scope"}[evidence boundaries] describe those additional interfaces.
The successful-return property has a successful source run as its antecedent;
totality and complete failure coverage require further arguments. This selected
application is stored compression, rather than a theorem about Level-1 or all
DEFLATE implementations.

The source nomination is lean-zip `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21`
with zip-common `4425bab1f9522307d77e8d485bc536149ba31c36`. The
[compression definition](https://github.com/kim-em/lean-zip/blob/273d0d6cd9cab77c7f3489b0b0b1f6e543315d21/Zip/Wasm/Stored.lean#L8)
and
[source roundtrip theorem](https://github.com/kim-em/lean-zip/blob/273d0d6cd9cab77c7f3489b0b0b1f6e543315d21/Zip/Spec/DeflateStoredCorrect.lean#L751)
were reviewed as Lean 4.33 source on 2026-10-05.
[The captured program](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/Fir/Compiler/LCNF/retained-example/RetainedRC2.lean.in#L10)
identifies the final-LCNF object used by FIR. These are source and capture
references; no fresh external build, transitive-axiom audit or Blueprint
association of the lean-zip theorem is claimed here.

# What is proved and what remains open
%%%
tag := "w6-theorem-menu"
%%%

The preceding argument distinguishes three kinds of result: an application
property in source Lean, local or conditional compiler execution theorems, and
a complete compiler guarantee for a selected program or all supported programs.
The current proof boundary is summarized below. The formal catalog records each
statement and the trust chapter explains its evidence.

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
