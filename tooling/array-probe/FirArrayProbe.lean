namespace FirArrayProbe

private def readLoop (values : Array UInt32) (index : Nat) :
    Nat → UInt32 → UInt32
  | 0, accumulator => accumulator
  | rounds + 1, accumulator =>
      readLoop values index rounds (accumulator + values[index]!)

/-- Repeat one ordinary checked Array read without rebuilding the input. -/
def readRepeated (values : Array UInt32) (index rounds : Nat) : UInt32 :=
  readLoop values index rounds 0

/-- Allocate the same fresh Array used by the mutation probes, but do not mutate it. -/
def buildOnly (size index : Nat) : UInt32 :=
  (Array.replicate size (1 : UInt32))[index]!

private def uniqueLoop (index : Nat) : Nat → Array UInt32 → Array UInt32
  | 0, values => values
  | rounds + 1, values =>
      uniqueLoop index rounds (values.set! index 7)

/-- Repeatedly update an exclusively owned Array. -/
def updateUnique (size index rounds : Nat) : UInt32 :=
  let values := Array.replicate size (1 : UInt32)
  (uniqueLoop index rounds values)[index]!

private def sharedLoop (index : Nat) :
    Nat → Array UInt32 → UInt32 → UInt32
  | 0, values, digest => digest + values[index]!
  | rounds + 1, values, digest =>
      let alias := values
      let updated := values.set! index 7
      sharedLoop index rounds updated (digest + alias[index]!)

/--
Retain the pre-update Array through every mutation. Each iteration therefore
observes a genuinely shared input and must preserve the alias by copying.
-/
def updateShared (size index rounds : Nat) : UInt32 :=
  let values := Array.replicate size (1 : UInt32)
  sharedLoop index rounds values 0

end FirArrayProbe
