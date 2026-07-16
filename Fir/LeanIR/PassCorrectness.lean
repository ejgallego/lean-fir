import Fir.LeanIR.Interpreter
import Fir.LeanIR.Pipeline

namespace Fir.LeanIR

open Lean
open Lean.Compiler

/-- A phase-specific semantic interface used by pass theorems. -/
structure PhaseSemantics (phase : LCNF.Phase) where
  Value : Type
  Observation : Type
  Evaluates : Program phase → Name → Array Value → Observation → Prop

def SamePhaseCorrect (semantics : PhaseSemantics phase) (before after : Program phase)
    (originalEntries : Array Name) : Prop :=
  ∀ entry, entry ∈ originalEntries → ∀ args observation,
    semantics.Evaluates before entry args observation ↔
      semantics.Evaluates after entry args observation

structure PhaseSimulation (source target : LCNF.Phase)
    (sourceSemantics : PhaseSemantics source) (targetSemantics : PhaseSemantics target) where
  valueRel : sourceSemantics.Value → targetSemantics.Value → Prop
  observationRel : sourceSemantics.Observation → targetSemantics.Observation → Prop

inductive ListRel (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel relation [] []
  | cons {left : α} {right : β} {leftTail : List α} {rightTail : List β}
      (head : relation left right) (tail : ListRel relation leftTail rightTail) :
      ListRel relation (left :: leftTail) (right :: rightTail)

def LoweringCorrect (sourceSemantics : PhaseSemantics source)
    (targetSemantics : PhaseSemantics target)
    (simulation : PhaseSimulation source target sourceSemantics targetSemantics)
    (before : Program source) (after : Program target) (originalEntries : Array Name) : Prop :=
  ∀ entry, entry ∈ originalEntries → ∀ sourceArgs targetArgs,
    ListRel simulation.valueRel sourceArgs.toList targetArgs.toList →
    ∀ sourceObservation,
      sourceSemantics.Evaluates before entry sourceArgs sourceObservation →
      ∃ targetObservation,
        targetSemantics.Evaluates after entry targetArgs targetObservation ∧
        simulation.observationRel sourceObservation targetObservation

namespace Impure

/-- Big-step behavior derived from the canonical small-step relation. -/
def Evaluates (externals : ExternalSpec) (program : ImpureProgram) (entry : Name)
    (args : Array Value) (observation : Observation) : Prop :=
  ∃ count final,
    Steps externals count (initialState program entry args) final ∧
    coreStep final = .done observation

def semantics (externals : ExternalSpec) : PhaseSemantics .impure :=
  { Value := Value
    Observation := Observation
    Evaluates := Evaluates externals }

structure AddressRenaming where
  forward : Location → Option Location
  reverse : Location → Option Location
  leftInverse : ∀ {left right}, forward left = some right → reverse right = some left
  rightInverse : ∀ {left right}, reverse right = some left → forward left = some right

inductive ValueRel (rho : AddressRenaming) : Value → Value → Prop where
  | tagged (payload : UInt64) :
      ValueRel rho (.object (.tagged payload)) (.object (.tagged payload))
  | heap {left right : Location} (mapped : rho.forward left = some right) :
      ValueRel rho (.object (.heap left)) (.object (.heap right))
  | usize (value : UInt64) : ValueRel rho (.usize value) (.usize value)
  | scalar (value : ScalarValue) : ValueRel rho (.scalar value) (.scalar value)
  | erased : ValueRel rho .erased .erased
  | reuseNone : ValueRel rho (.reuseToken none) (.reuseToken none)
  | reuseSome {left right : Location} (mapped : rho.forward left = some right) :
      ValueRel rho (.reuseToken (some left)) (.reuseToken (some right))

def ArrayRel (relation : α → β → Prop) (left : Array α) (right : Array β) : Prop :=
  ListRel relation left.toList right.toList

inductive HeapObjectRel (rho : AddressRenaming) : HeapObject → HeapObject → Prop where
  | ctor {left right : ConstructorObject}
      (tag : left.tag = right.tag)
      (objects : ArrayRel (ValueRel rho) left.objectFields right.objectFields)
      (usizes : left.usizeFields = right.usizeFields)
      (scalars : left.scalarFields = right.scalarFields) :
      HeapObjectRel rho (.ctor left) (.ctor right)
  | closure {leftFixed rightFixed : Array Value} {function : Name} {arity : Nat}
      (fixed : ArrayRel (ValueRel rho) leftFixed rightFixed) :
      HeapObjectRel rho (.closure function arity leftFixed)
        (.closure function arity rightFixed)
  | boxed {type : Expr} {left right : Value}
      (value : ValueRel rho left right) :
      HeapObjectRel rho (.boxed type left) (.boxed type right)
  | string (value : String) : HeapObjectRel rho (.string value) (.string value)
  | natural (value : Nat) : HeapObjectRel rho (.natural value) (.natural value)
  | byteArray (value : Array UInt8) :
      HeapObjectRel rho (.byteArray value) (.byteArray value)
  | opaque (typeName : Name) : HeapObjectRel rho (.opaque typeName) (.opaque typeName)

def HeapCellRel (rho : AddressRenaming) (left right : HeapCell) : Prop :=
  left.rc = right.rc ∧
  left.persistent = right.persistent ∧
  left.live = right.live ∧
  HeapObjectRel rho left.object right.object

inductive Reachable (heap : Heap) (roots : List Value) : Location → Prop where
  | root {location : Location}
      (member : Value.object (.heap location) ∈ roots) : Reachable heap roots location
  | child {parent child : Location} {cell : HeapCell} {value : Value}
      (parentReachable : Reachable heap roots parent)
      (cellFound : findCell? heap parent = some cell)
      (member : value ∈ cell.object.ownedValues.toList)
      (reference : value = .object (.heap child)) : Reachable heap roots child

def HeapRel (rho : AddressRenaming) (left right : Heap)
    (leftRoots rightRoots : List Value) : Prop :=
  (∀ location, Reachable left leftRoots location →
    ∃ mapped leftCell rightCell,
      rho.forward location = some mapped ∧
      findCell? left location = some leftCell ∧
      findCell? right mapped = some rightCell ∧
      HeapCellRel rho leftCell rightCell) ∧
  (∀ location, Reachable right rightRoots location →
    ∃ mapped rightCell leftCell,
      rho.reverse location = some mapped ∧
      findCell? right location = some rightCell ∧
      findCell? left mapped = some leftCell ∧
      HeapCellRel rho leftCell rightCell)

def EventRel (rho : AddressRenaming) (left right : ExternalEvent) : Prop :=
  left.name = right.name ∧
  ArrayRel (ValueRel rho) left.args right.args ∧
  ValueRel rho left.result right.result

def OutcomeRel (rho : AddressRenaming) : Outcome → Outcome → Prop
  | .returned left, .returned right => ValueRel rho left right
  | .fault left, .fault right => left = right
  | _, _ => False

def Observation.roots (observation : Observation) : List Value :=
  let outcomeRoots :=
    match observation.outcome with
    | .returned value => [value]
    | .fault _ => []
  outcomeRoots ++ observation.trace.toList.flatMap fun event =>
    event.result :: event.args.toList

/-- Observable equality ignores addresses and heap cells unreachable from observable roots. -/
def ObservationRel (left right : Observation) : Prop :=
  ∃ rho : AddressRenaming,
    OutcomeRel rho left.outcome right.outcome ∧
    left.world = right.world ∧
    ArrayRel (EventRel rho) left.trace right.trace ∧
    HeapRel rho left.heap right.heap left.roots right.roots

theorem samePhaseCorrect_refl (externals : ExternalSpec) (program : ImpureProgram)
    (entries : Array Name) :
    SamePhaseCorrect (semantics externals) program program entries := by
  intro entry _ args observation
  rfl

end Impure

end Fir.LeanIR
