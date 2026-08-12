namespace Fir.Wasm.Emit.SourceClosedFixture

private def pushUInt32LE (bytes : ByteArray) (word : UInt32) : ByteArray :=
  (((bytes.push word.toUInt8).push (word >>> 8).toUInt8).push
    (word >>> 16).toUInt8).push (word >>> 24).toUInt8

/-- Seed the imported specialization and closed-term caches. -/
def wordTable : Array UInt32 :=
  (Array.range 33).map (fun index => index.toUInt32)

/--
Imported source fixture whose ordinary module compilation and isolated
final-LCNF recompilation extract typed closed terms in a different order.
-/
def packedTable : ByteArray :=
  let words := (Array.range 33).map (fun index => index.toUInt32)
  words.foldl pushUInt32LE ByteArray.empty

end Fir.Wasm.Emit.SourceClosedFixture
