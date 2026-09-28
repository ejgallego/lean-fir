import Verso
import VersoManual
import VersoBlueprint
import FirTalos.ConcreteRootedTerminal
import FirTalos.ConcreteFaultCorrectness
import FirTalos.ConcreteFinalLcnfTyping
import FirTalos.ConcreteSupportedPipeline
import FirTalos.ConcreteRegionEntry
import FirTalos.ConcretePublicationValidation

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "W6: from validated compiler output to execution" =>

This pilot describes the accepted FIR argument at commit `81bb0e2ab`.
The goal is to make missing premises and useful next contributions visible.
Associated declarations are checked against the checkout used to build this
site. The commit above dates the reviewed narrative; it is not a claim that a
later checkout has been reviewed.

*Reading the graph.* An arrow is a mathematical dependency. Existing nodes
use Lean dependency inference; open nodes have explicitly authored proof plans.
A proved conditional result and a theorem eliminating its premise are separate
nodes. Tags describe our editorial classification; they do not change
Blueprint's computed status. Resource contracts remain explicit execution
conditions. Integration and axiom evidence are discussed in the evaluation
chapter, separately from the graph's formalization colors.

:::author "w6" (name := "FIR W6 proof lane")
:::
:::author "root" (name := "FIR integration owner")
:::

:::group "contracts"
Observable contracts
:::
:::group "compiler"
Compiler facts
:::
:::group "construction"
Heap construction
:::
:::group "execution"
Execution
:::
:::group "frontier"
Open obligations
:::

# Observable contracts

:::definition "return-post" (parent := "contracts") (lean := "FirTalos.Concrete.RefinedReturnPost") (autoDeps := true)
A successful target return represents the exact source value at the specified
ABI kind. One refinement witness relates the live heap, globals, world and
ordered external trace, with no target runtime failure and the precise return
stack. The ABI is chosen by the export; existentially choosing a convenient
kind would weaken the contract.
:::

:::definition "fault-post" (parent := "contracts") (lean := "FirTalos.Concrete.RefinedFaultPost") (autoDeps := true)
A target trap represents the source's structured semantic fault under a common
heap/runtime witness. An unrelated target memory trap or ABI mismatch does not
satisfy this contract merely because both executions stopped.
:::

:::definition "prefix-contract" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteFiniteTraceCorrect") (autoDeps := true)
Every finite source execution prefix has a finite target path with matching
world and ordered external observations. This definition alone does not
constrain the terminal returned value. See {bpref "return-post"}[] for that
additional requirement.
:::

:::definition "admission-interface" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteStructuredCompilerCurrentStepAdmission") (autoDeps := true)
For every supported function, recursively validated current outcome and
successful source step, recover current-node admission and its exact allocation
cost. This is a quantified compiler law. Having defined this structure does
not construct an inhabitant for every supported program.
:::

:::definition "address-space" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteStructuredCurrentStepAddressSpaceSafety") (autoDeps := true)
Allocation-producing steps have sufficient wasm32 address space at their
actual frame budget. This execution condition is deliberately retained. It is
not an open compiler lemma whose eventual proof promises unbounded memory.
:::

# Compiler-derived facts

:::theorem "supported-export" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.exists_ofSupportedPipeline") (autoDeps := true)
The supported compilation pipeline constructs a concrete supported export from
its checked source and generated module. The closure-flow condition remains
explicit. This establishes static export identity and alignment, not dynamic
admission for all future states.
:::

:::theorem "rooted-entry" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.rootedPreciseCodeGlobalRoot") (autoDeps := true)
A supported export constructs its initial rooted, precise relation from cache
alignment and the entry runtime invariant. It retains the export's selected
result kind. The caller supplies neither a new simulation invariant nor a
future target path.
:::

:::theorem "case-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeCoreRel.admit_cases_of_validated_step") (autoDeps := true)
A validated case node and successful source step yield exact case admission.
Normalization, discriminator selection and default/scalar/object branches are
compiler-derived. This is one completed branch of the admission audit.
:::

:::theorem "direct-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_directCall_of_compiler") (autoDeps := true)
A validated direct call yields zero-cost admission given its exact semantic
argument row at the compiler-selected ABI. Compiler local identities and call
site equations are derived. Non-directional object-family argument provenance
remains an input; see {bpref "provenance-closure"}[].
:::

:::theorem "return-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_return_of_compiler") (autoDeps := true)
Return admission is derived at cost zero from the validated outcome and its
use-site provenance. A genuinely non-directional object-family return still
requires the precise producer origin.
:::

:::definition "lazy-miss-boundary" (parent := "compiler") (lean := "FirTalos.Concrete.ConcreteStructuredLazyMissBackendCoverageAt") (autoDeps := true)
The present lazy-miss coverage boundary requires an internal supported
initializer and excludes object and tobject result kinds. This is a description
of the current restriction, not evidence that all supported source misses
satisfy it. General heap-result closure is {bpref "heap-miss-closure"}[].
:::

:::theorem "lazy-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_lazy_of_compiler") (autoDeps := true)
The runtime lookup chooses hit or miss. Validation constructs exact lazy-call
admission, conditional on the miss-only backend coverage boundary. Cache hits
need no such miss evidence. The object/tobject exclusions remain visible in
{bpref "lazy-miss-boundary"}[].
:::

# Constructing and publishing a fresh heap result

:::theorem "construction-entry" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredLazyCallReadyFocus.enterRegion") (autoDeps := true)
Actual lazy-miss entry establishes an active construction region at the
callee's entry cutoff. The original resource scope is retained throughout
construction. This local relation does not yet provide the general suspended
validated lazy-frame companion.
:::

:::theorem "construction-return" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredRegionCodeCore.advance_return") (autoDeps := true)
An active construction region, aligned locals, returned heap lookup and fresh
root produce the exact source return, two target instructions, and a fresh
yield relation. Root freshness remains a hypothesis; ABI representation and
the execution path are derived.
:::

:::theorem "publication" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredFreshYieldCore.publishAtRoot") (autoDeps := true)
Fresh yield evidence and the saved caller/publication premises reconnect cache
publication with the rooted global relation. This is an executable local
consumer of construction evidence. The general heap-miss dispatcher does not
yet derive all of its inputs automatically.
:::

# What the current endpoints establish

:::theorem "rooted-steps" (parent := "execution") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.rootedExecSteps_of_currentStepAdmission") (autoDeps := true)
Given current-step admission, address-space safety and the entry contract,
every finite source execution produces a target path retaining the original
root ABI and matching prefix observations. The witness may evolve with
allocation; it is not fixed to the entry witness.
:::

:::theorem "conditional-return" (parent := "execution") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteSupportedExport.terminatesWith_of_rootedExecEvaluates") (autoDeps := true)
Successful source evaluation yields actual export termination with the exact
source observation and result ABI. Current-step admission, address-space
safety, cache alignment, arity and the entry runtime relation remain explicit.
This theorem is proved. Closing its compiler-owned premise is the distinct
open target {bpref "admission-closure"}[].
:::

:::theorem "conditional-fault" (parent := "execution") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteSupportedExport.faultCorrectOfSimulation") (autoDeps := true)
A syntax-directed concrete fault simulation gives source evaluation to the
specified fault and an executable target trap satisfying the refined fault
postcondition. The simulation certificate is supplied. Constructing it for
general supported faulting executions is {bpref "fault-closure"}[].
:::

# Open proof frontier

These nodes are reviewed descriptions of missing results, with proposed
mathematical dependencies. They have no associated completed declaration.
Their exact contribution statements still need W6 review; a graph status of
"ready to formalize" is not authorization to publish them as immutable tasks.
There are no placeholder Lean proofs in this documentation package.

:::theorem "provenance-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (priority := "high")
Derive the exact non-directional call-argument and return producer facts from
the compiler-supported program and the internally maintained relation. Do not
introduce a caller-supplied universal provenance invariant.
:::
:::proof "provenance-closure"
Proposed route: identify each producer/use boundary left by the directional
refinement lemmas, preserve the smallest semantic origin fact, and feed the
existing admission consumers {bpref "direct-admission"}[] and
{bpref "return-admission"}[]. These consumer links are not proof dependencies.
The precise statement is pending owner review.
:::

:::theorem "heap-miss-closure" (parent := "frontier") (owner := "w6") (tags := "open, active-design") (priority := "high")
Extend the internally maintained validated machine relation so supported heap
initializer misses carry construction evidence through intermediate states,
suspended callers, return, publication and bind. Derive admission for those
misses without excluding object/tobject results by assumption.
:::
:::proof "heap-miss-closure" (uses := "construction-entry, construction-return, publication")
Compose the fixed-entry construction relation with a saved validated caller
companion. Existing local paths are ingredients. The central relation and
consumer still need assembly; this is active W6 design work.
:::

:::theorem "admission-closure" (parent := "frontier") (owner := "w6") (tags := "open") (priority := "high") (uses := "admission-interface")
Construct the current-step admission law from production validation and the
internal semantic relation for every successful guarded source step. Retain
finite runtime and external execution contracts explicitly.
:::
:::proof "admission-closure" (uses := "case-admission, direct-admission, return-admission, lazy-admission, provenance-closure, heap-miss-closure")
Assemble the 20 branches in the admission audit, including the external and
object/schema families not expanded in this pilot. The displayed branch
selection is an overview, not an exhaustive kernel-checked decomposition.
:::

:::theorem "fault-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "fault-post")
For a supported source execution ending in a semantic fault, derive the
corresponding executable target fault under explicit runtime/resource
contracts, without a client-supplied fault-simulation certificate.
:::
:::proof "fault-closure" (uses := "conditional-fault")
The existing certificate-based theorem supplies a consumer. The general
construction and its relation to the successful-step simulation require a
separate argument; successful-return closure alone does not imply it.
:::

:::theorem "closed-export" (parent := "frontier") (owner := "w6") (tags := "open") (priority := "high") (uses := "return-post, fault-post, prefix-contract, address-space")
A compiler-produced supported export preserves finite observations and
represented terminal returns or semantic faults, with compiler-owned
admission derived internally. Entry, external-runtime and finite-resource
conditions remain explicit. No caller-chosen future path or program
simulation certificate is accepted.
:::
:::proof "closed-export" (uses := "supported-export, rooted-entry, rooted-steps, conditional-return, admission-closure, fault-closure")
Supply compiler-derived admission to the existing execution chain and compose
the general fault counterpart. This is the pilot's top-level target.
:::

:::theorem "resident-linking" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "return-post, fault-post")
Replace the contracted resident operations used by the compiler theorem with
execution of their installed implementations, retaining explicit genuinely
external operations and finite resources. State the resulting linked execution
boundary precisely before claiming a theorem about encoded artifact bytes.
:::
:::proof "resident-linking" (uses := "closed-export")
Compose helper implementation refinements and installation/import closure
with the contracted compiler theorem. Generation tests and linked artifact
tests supply separate evidence; they do not discharge the semantic proof.
:::
