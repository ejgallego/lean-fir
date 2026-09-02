namespace Fir.Wasm.Emit.SourceOwnershipFixture

/-- An exported reference parameter is owned by Lean's native entry ABI. -/
@[export fir_source_owned_entry_fixture]
def ownedEntry (_value : Array Nat) : Unit := ()

/-- An explicit source borrow remains borrowed for an isolated logical root. -/
def borrowedEntry (_value : @& Array Nat) : Unit := ()

end Fir.Wasm.Emit.SourceOwnershipFixture
