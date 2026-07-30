import Init.Data.Format.Basic
import Init.Data.String.Basic

namespace Fir.LCNFC.PrettyM

/--
One exact operation observed at the `Std.Format.MonadPrettyFormat` boundary.

The numeric event kinds match the FIR-native browser facade:
`0` is output, `1` is newline, `2` is start-tag, and `3` is end-tags.
-/
structure Event where
  kind : Nat
  text : String
  value : Nat

/-- A rendered string and its reverse-chronological formatting event stream. -/
structure Trace where
  text : String
  eventsRev : List Event

private structure RenderState where
  out : String := ""
  eventsRev : List Event := []
  column : Nat := 0

private abbrev RenderM (α : Type) := Nat → α × Nat

@[reducible] private def renderMonad : Monad RenderM where
  pure value := fun raw => (value, raw)
  bind action next := fun raw =>
    let (value, raw) := action raw
    next value raw

@[reducible] private unsafe def monadPrettyFormat :
    Std.Format.MonadPrettyFormat RenderM where
  pushOutput string := fun raw =>
    let state : RenderState := unsafeCast raw
    ((), unsafeCast ({
      out := String.Internal.append state.out string
      eventsRev := { kind := 0, text := string, value := 0 } :: state.eventsRev
      column := state.column + String.Internal.length string } : RenderState))
  pushNewline indent := fun raw =>
    let state : RenderState := unsafeCast raw
    ((), unsafeCast ({
      out := String.Internal.append state.out
        (String.Internal.pushn "\n" ' ' indent)
      eventsRev := { kind := 1, text := "", value := indent } :: state.eventsRev
      column := indent } : RenderState))
  currColumn := fun raw =>
    let state : RenderState := unsafeCast raw
    (state.column, raw)
  startTag tag := fun raw =>
    let state : RenderState := unsafeCast raw
    ((), unsafeCast ({
      state with
      eventsRev := { kind := 2, text := "", value := tag } :: state.eventsRev
    } : RenderState))
  endTags count := fun raw =>
    let state : RenderState := unsafeCast raw
    ((), unsafeCast ({
      state with
      eventsRev := { kind := 3, text := "", value := count } :: state.eventsRev
    } : RenderState))

/--
Run the same monomorphic `Std.Format.prettyM` observation used by the
FIR-native facade. This implementation stays local because the C pipeline
links the pinned Lean runtime, Init, and Std archives rather than `libFir`.
-/
private unsafe def render
    (format : Std.Format) (width indent column : Nat) : Trace :=
  let action : RenderM Unit :=
    @Std.Format.prettyM RenderM format width indent renderMonad monadPrettyFormat
  let initial : Nat := unsafeCast ({ column } : RenderState)
  let result : RenderState := unsafeCast (action initial).2
  { text := result.out, eventsRev := result.eventsRev }

private def maximumRequestBytes : Nat := 64 * 1024 * 1024
private def maximumNodes : Nat := 1_000_000
private def maximumNaturalLimbs : Nat := 1_000_000
private def limbBase : Nat := 4294967296

private structure Cursor where
  input : ByteArray
  position : Nat := 0
  nodes : Nat := 0

private abbrev Parser (α : Type) := StateT Cursor (Except String) α

private def parseError (message : String) : Parser α :=
  throw message

private def readByte : Parser UInt8 := do
  let cursor ← get
  if h : cursor.position < cursor.input.size then
    let byte := cursor.input[cursor.position]
    set { cursor with position := cursor.position + 1 }
    pure byte
  else
    parseError "unexpected end of prettyM request"

private def expectByte (expected : UInt8) (label : String) : Parser Unit := do
  let actual ← readByte
  unless actual == expected do
    parseError s!"invalid prettyM request {label}"

private def readUInt32 : Parser Nat := do
  let byte0 ← readByte
  let byte1 ← readByte
  let byte2 ← readByte
  let byte3 ← readByte
  pure (byte0.toNat +
    byte1.toNat * 256 +
    byte2.toNat * 65536 +
    byte3.toNat * 16777216)

private def readNatural : Parser Nat := do
  let count ← readUInt32
  if count == 0 then
    parseError "natural has no limbs"
  if count > maximumNaturalLimbs then
    parseError "natural exceeds the prettyM limb limit"
  let mut value := 0
  let mut scale := 1
  let mut mostSignificant := 0
  for _ in [0:count] do
    let limb ← readUInt32
    value := value + limb * scale
    scale := scale * limbBase
    mostSignificant := limb
  if count > 1 && mostSignificant == 0 then
    parseError "natural has a non-canonical leading zero limb"
  pure value

private def readInteger : Parser Int := do
  let sign ← readByte
  let magnitude ← readNatural
  match sign with
  | 0 => pure (Int.ofNat magnitude)
  | 1 =>
      if magnitude == 0 then
        parseError "integer has a negative zero encoding"
      pure (Int.negOfNat magnitude)
  | _ => parseError "integer sign is invalid"

private def readString : Parser String := do
  let length ← readUInt32
  let cursor ← get
  let stop := cursor.position + length
  if stop > cursor.input.size then
    parseError "string exceeds the prettyM request"
  let mut bytes := ByteArray.emptyWithCapacity length
  for offset in [0:length] do
    bytes := bytes.push cursor.input[cursor.position + offset]!
  set { cursor with position := stop }
  match String.fromUTF8? bytes with
  | some string => pure string
  | none => parseError "prettyM request contains invalid UTF-8"

private def beginNode : Parser Unit := do
  let cursor ← get
  if cursor.nodes >= maximumNodes then
    parseError "format exceeds the prettyM node limit"
  set { cursor with nodes := cursor.nodes + 1 }

private partial def readFormat : Parser Std.Format := do
  beginNode
  let tag ← readByte
  match tag with
  | 0 => pure .nil
  | 1 => pure .line
  | 2 =>
      let force ← readByte
      match force with
      | 0 => pure (.align false)
      | 1 => pure (.align true)
      | _ => parseError "Format.align flag is invalid"
  | 3 => pure (.text (← readString))
  | 4 =>
      let indent ← readInteger
      pure (.nest indent (← readFormat))
  | 5 =>
      let left ← readFormat
      pure (.append left (← readFormat))
  | 6 =>
      let behavior ← readByte
      let body ← readFormat
      match behavior with
      | 0 => pure (.group body .allOrNone)
      | 1 => pure (.group body .fill)
      | _ => parseError "Format.group behavior is invalid"
  | 7 =>
      let value ← readNatural
      pure (.tag value (← readFormat))
  | _ => parseError "Format node tag is invalid"

private def readRequest : Parser (Std.Format × Nat × Nat × Nat) := do
  expectByte 0x46 "magic"
  expectByte 0x50 "magic"
  expectByte 0x4d "magic"
  expectByte 0x31 "version"
  let width ← readNatural
  let indent ← readNatural
  let column ← readNatural
  let format ← readFormat
  let cursor ← get
  unless cursor.position == cursor.input.size do
    parseError "prettyM request has trailing bytes"
  pure (format, width, indent, column)

private def pushUInt32 (output : ByteArray) (value : Nat) : ByteArray :=
  output
    |>.push (UInt8.ofNat value)
    |>.push (UInt8.ofNat (value / 256))
    |>.push (UInt8.ofNat (value / 65536))
    |>.push (UInt8.ofNat (value / 16777216))

private partial def naturalLimbs (value : Nat) : Array Nat :=
  let rec loop (remaining : Nat) (limbs : Array Nat) : Array Nat :=
    let limbs := limbs.push (remaining % limbBase)
    let remaining := remaining / limbBase
    if remaining == 0 then limbs else loop remaining limbs
  loop value #[]

private def pushNatural (output : ByteArray) (value : Nat) : ByteArray :=
  let limbs := naturalLimbs value
  limbs.foldl pushUInt32 (pushUInt32 output limbs.size)

private def pushString (output : ByteArray) (value : String) : ByteArray := Id.run do
  let bytes := value.toUTF8
  let mut output := pushUInt32 output bytes.size
  for index in [0:bytes.size] do
    output := output.push bytes[index]!
  output

private def responsePrefix (seed : ByteArray) (status : UInt8) : ByteArray :=
  (ByteArray.emptyWithCapacity (min seed.size 64))
    |>.push 0x46
    |>.push 0x50
    |>.push 0x52
    |>.push 0x31
    |>.push status

private def errorResponse (seed : ByteArray) (message : String) : ByteArray :=
  pushString (responsePrefix seed 1) message

private def successResponse (seed : ByteArray) (trace : Trace) : ByteArray :=
  let events := trace.eventsRev.reverse
  let output := pushString (responsePrefix seed 0) trace.text
  let output := pushUInt32 output events.length
  events.foldl (init := output) fun output event =>
    pushNatural (pushString (output.push (UInt8.ofNat event.kind)) event.text)
      event.value

/--
Bulk Emscripten bridge entry point.

The input and output use `fir.prettyM.emscripten-wire/v1`. Protocol failures
are returned as status-bearing byte arrays, so the C bridge always owns a
single ordinary `ByteArray → ByteArray` Lean call.
-/
@[export fir_lcnf_c_pretty_render_wire]
unsafe def renderWire (input : ByteArray) : ByteArray :=
  if input.size > maximumRequestBytes then
    errorResponse input "prettyM request exceeds 64 MiB"
  else
    match readRequest.run { input } with
    | .error message => errorResponse input message
    | .ok ((format, width, indent, column), _) =>
        successResponse input (render format width indent column)

end Fir.LCNFC.PrettyM
