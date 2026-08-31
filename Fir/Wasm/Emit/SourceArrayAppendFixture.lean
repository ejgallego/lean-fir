namespace Fir.Wasm.Emit.SourceArrayAppendFixture

/--
An imported source entry whose generated outer `List.foldl` specialization
calls the specialization produced by `Array.appendList`. This keeps the
cross-module specialization-owner recovery path observable without naming a
consumer declaration.
-/
def appendNestedArrays (rows : List (List Nat)) : Array Nat :=
  rows.foldl (init := #[]) fun values row => values.appendList row

end Fir.Wasm.Emit.SourceArrayAppendFixture
