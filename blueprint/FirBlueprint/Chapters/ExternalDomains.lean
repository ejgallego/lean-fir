import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "External contracts and request domains" =>
%%%
tag := "external-domains"
%%%

This chapter records the external-contract proposal and its request domains.
Interfaces and the checked Nat slice were reviewed at FIR `b83df9155`; the
Int and rejecting-implementation probes were checked at `471d0fc9f`.
The global
{bpref "external-spec"}[] remains a hole. Describing a candidate clause does
not make it the adopted specification.

# Three questions and their consumers

{bpref "external-spec"}[] describes what a primitive does.
{bpref "external-realization"}[] asks whether a named intended implementation
provides that behavior on a meaningful domain.
{bpref "external-admission"}[] derives the compiler-side facts needed to
simulate a successful contracted call. These are different obligations.

{name Fir.LeanIR.Impure.ExternalSpec}`ExternalSpec` relates a request, incoming runtime and complete response.
The request contains the name, parameter types, result type and argument values.
The response contains the returned value, heap, next allocation location and
world. {name Fir.LeanIR.Impure.resumeExternal}`resumeExternal` adds the external event to the interpreter trace;
the response neither supplies nor replaces that trace. The contract uses the
runtime of the staged waiting state at which the implementation is called.

A source clause should state the operation's arithmetic or effect, not merely
that its response has some admissible shape. The pure admission constructors
accept an existential result value; their shape/cost equations alone do not
say that a call named {name}`Nat.add` adds its operands.

# The checked Nat domain and response

For a runtime $`s`, {name FirBlueprint.Targets.NatArgument}`NatArgument` relates $`v` to $`n` when $`v` is a tagged payload with
natural value $`n`, or a heap reference whose live cell contains {name Fir.LeanIR.Impure.HeapObject.natural}`.natural` $`n`.
Heap liveness comes from the actual decoder's successful lookup. This is not
yet a compiler ABI or runtime-validity predicate for every admitted payload.

The existing definitions read as follows:

For $`q` a request, $`s` an incoming runtime and $`x,y\in\mathbb{N}`,
write $`A(s,v,n)` for {name FirBlueprint.Targets.NatArgument}`NatArgument` applied to $`s,v,n`. Then

$$`\begin{aligned}
\operatorname{Inputs}(q,s,x,y)\iff{}&q.\mathrm{name}=\mathrm{Nat.add}\ \land\ \exists v_x,v_y,\\
&q.\mathrm{args}=[v_x,v_y]\land A(s,v_x,x)\land A(s,v_y,y).
\end{aligned}`

Writing $`N(s,n)` for {name FirTalos.Concrete.semanticNaturalExternalResponse}`semanticNaturalExternalResponse` applied to $`s,n`, the response
relation is

$$`\operatorname{Response}(q,s,r)\iff\exists x,y,\ \operatorname{Inputs}(q,s,x,y)\land r=N(s,x+y).`

These are notation for the associated existing definitions, not new predicates.
The complete response $`r` includes heap, allocation cursor and world.

{bpref "nat-add-contract"}[] associates the real definition.
{bpref "nat-add-realization"}[] proves the actual validation dispatcher succeeds
and returns that response for every request in this domain. The proof covers
tagged, heap and mixed arguments, and tagged or allocating results, with exact
heap/cursor/world behavior. It uses the original private handler rather than
a copy. Metadata is unrestricted because that handler ignores it.

The original proposal also required `ValidNatBinaryMetadata(q)`. That predicate
was schematic and remains unimplemented. Declaration type metadata, ABI
compatibility and representation bounds require review at the compiler boundary;
an ABI lane alone does not distinguish Nat from Int.

## Metadata guards must match the implementation claim

{name Fir.LeanIR.Impure.ExternalImpl.Implements}`ExternalImpl.Implements` has the following meaning:

For implementation $`I` and specification relation $`S`,

$$`\operatorname{Implements}(I,S)\iff\forall q,s,r,\ I.\mathrm{call}(q,s)=\operatorname{ok}(r)\Rightarrow S(q,s,r).`

It does not restrict that implication to compiler-valid requests. Since the
checked Nat handler succeeds for arbitrary metadata, a clause requiring a
metadata guard that can fail cannot describe all those successful responses.
This follows from the interface and checked handler theorem; it is a contract
design issue, not a newly tested implementation defect.

Options to review are a handler contract broad enough to cover its successes,
with compiler metadata derived separately; an explicitly restricted adapter
whose behavior is part of the intended implementation; or a domain-relative
correctness interface, with domain membership proved at every relevant source
call. The latter two require an explicit implementation/interface decision.
The existing Nat slice uses the first approach. No change to the global
{name Fir.LeanIR.Impure.ExternalImpl.Implements}`Implements` interface or endpoint is made here.

# Candidate primitive clauses and effects

These are the eleven names in the reviewed pure admission inventory, not a
complete enumeration of calls accepted by lowering or validation.

:::table +header
*
  * Primitive
  * Decoded inputs and mathematical result
  * Candidate response
*
  * {name}`Int.ofNat`
  * {name}`Nat` $`x`; integer result of {name}`Int.ofNat` applied to $`x`
  * Int representation decision below
*
  * {name}`Int.neg`
  * {name}`Int` $`x`; $`-x`
  * Int representation decision below
*
  * {name}`Int.add`, {name}`Int.sub`
  * {name}`Int` $`x`, $`y`; $`x+y`, $`x-y`
  * Int representation decision below
*
  * {name}`Int.natAbs`
  * {name}`Int` $`x`; result of {name}`Int.natAbs` applied to $`x`
  * Semantic natural response
*
  * {name}`Nat.add`, {name}`Nat.sub`
  * {name}`Nat` $`x`, $`y`; sum or truncated subtraction
  * Semantic natural response; only the Nat-addition realization is associated here
*
  * {name}`Int.decLt`
  * {name}`Int` $`x`, $`y`; truth of $`x < y`
  * Semantic scalar response, {name}`UInt8` zero or one
*
  * {name}`Nat.decEq`, {name}`Nat.decLt`, {name}`Nat.decLe`
  * {name}`Nat` $`x`, $`y`; truth of equality, $`<`, $`\leq`
  * Semantic scalar response, {name}`UInt8` zero or one
:::

Pure clauses preserve world. Scalar clauses preserve heap and next location.
Nat responses use the exact allocation behavior of {name Fir.LeanIR.Impure.literal}`literal`. Int responses
must reflect the reviewed representation choice. Initializer calls, mutating
operations and effects require their own clauses. The validation dispatcher
also includes {name}`Nat.mul`, strings and arrays. Leaving a family unreviewed does
not justify defining its successful executions away with a false clause.

## The Int representation decision

The reviewed W6 {name Fir.Wasm.Concrete.semanticIntegerExternalResponse}`semanticIntegerExternalResponse` always allocates an integer
at the incoming {name Fir.LeanIR.Impure.RuntimeState.nextLocation}`nextLocation`; its cost model includes that allocation even
for zero. Validation's `encodeIntValue` uses a signed-32-bit tagged value when
possible. The recorded {InlineLean.lean}`Int.ofNat 0` probe returned tagged zero, preserving
heap and cursor, and could not equal any W6 canonical integer response.

One option preserves validation behavior and makes the W6 response, refinement
and cost model representation-aware. The alternative is an explicit
normalization bridge with proofs about observations and ownership. The former
is the review recommendation; W6/root own the decision. Its first acceptance
case is {InlineLean.lean}`Int.ofNat 0`, aligning response, heap effects, refinement and cost.
The discrepancy is recorded in
`bugs/FIR-BUG-impure-none-external-int-response-contract.md`. It blocks claiming
that the current contract covers validation; it does not refute the conditional
compiler theorem as stated.

# Realization includes availability on a stated domain

An implementation rejecting every call satisfies {name Fir.LeanIR.Impure.ExternalImpl.Implements}`Implements` for every
specification. Therefore existence of some implementation is insufficient
evidence of a useful specification, including for an always-false relation.

The rejecting-implementation probe is a small reproducible input for this
adequacy review, using FIR's actual definitions:

```
open Fir.LeanIR.Impure

example (specification : ExternalSpec) :
    rejectExternals.Implements specification := by
  intro request before response called
  cases called
```

It was checked at the source checkpoint above; this transcription installs no
new production declaration.

The intended realization shape names the implementation and adds availability.
For a reviewed domain predicate $`D`, the proposed requirements are

$$`\operatorname{Implements}(I,S)\quad\land\quad\forall q,s,\ D(q,s)\Rightarrow\exists r,\ I.\mathrm{call}(q,s)=\operatorname{ok}(r).`

Here $`I` names the intended implementation, rather than an existentially
chosen implementation, and $`D` remains a domain to review.

Define the domain independently of handler success and compiler admission,
and show which intended workload requests belong to it. An empty domain
would repeat the vacuity problem. State arity, metadata policy, argument
decoding and resource conditions explicitly. Family-by-family growth is
reasonable if its omissions remain visible. Failures or behavior outside the
domain are separate claims, subject to the chosen correctness interface.

The successful-return theorem already assumes successful source evaluation;
this specification-adequacy review does not add global totality as a new
premise. Source-handler realization also does not prove
{bpref "resident-linking"}[] for the installed Wasm helpers.

# What remains at the compiler boundary

{bpref "nat-add-admission"}[] consumes an existing {name FirTalos.Concrete.ExternalCallShape}`ExternalCallShape`, decoded
Nat operands, a {name Fir.Wasm.AbiKind.tobject}`.tobject` result kind and equal parameter/argument ABI rows.
It derives the canonical response and constructs natural-result admission at
{name Fir.Wasm.Concrete.naturalAllocationBytes}`naturalAllocationBytes` applied to $`x+y`. The general call shape provides directional
argument refinement, which does not imply that row equality.

{bpref "nat-add-site"}[] tracks construction of those inputs from the guarded
validator/source-step boundary. Review either a slice that derives equality
or a generalized production consumer. The global {bpref "external-admission"}[]
must also derive operation coverage, compiled signatures, provenance, result
ABI and exact cost. Those compiler facts do not belong inside the primitive
source specification.

Before freezing a contributor statement, settle the intended implementation
and Int model, the request/domain metadata policy, coverage beyond the pure
inventory, and initializer/effect clauses. These decisions remain open; the
chapter makes them reviewable without choosing a new global formal signature.

# Source evidence

`Fir/LeanIR/Runtime.lean` supplies requests, responses and {name Fir.LeanIR.Impure.ExternalImpl.Implements}`Implements`;
`Fir/LeanIR/Interpreter.lean` supplies staging and resumption.
`Fir/Validation/LCNF.lean` contains the decoders and actual handlers.
`Fir/Wasm/Concrete/ExternalCorrectness.lean` and
`IntegerAllocationCorrectness.lean` contain the reviewed Int model/cost.
`FirTalos/ConcreteRuntime.lean` supplies Nat/scalar responses;
`ConcreteCompilerCorrectness.lean` supplies the pure admission families;
`ConcreteResumableWasm.lean` supplies the quantified admission law.
The source audit maps wider branch and lazy-miss coverage.

The source objects at `38ecc9729` and `d2bf07a7e` retain the Nat handler and
conditional admission proof checkpoints. This chapter and the associated W6
nodes maintain their mathematical reading and remaining obligations.
