import Init.Data.Format.Basic
import Init.Data.String.Basic
import VersoSlides.Pretty

namespace Fir.LCNFC.PrettyMHtml

open VersoSlides

private def maximumRequestBytes : Nat := 64 * 1024 * 1024
private def maximumNodes : Nat := 1_000_000
private def maximumNaturalLimbs : Nat := 1_000_000
private def limbBase : Nat := 4294967296
private def maximumAnnotations : Nat := 1_000_000

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
    parseError "unexpected end of prettyM HTML request"

private def expectByte (expected : UInt8) (label : String) : Parser Unit := do
  let actual ← readByte
  unless actual == expected do
    parseError s!"invalid prettyM HTML request {label}"

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
    parseError "natural exceeds the prettyM HTML limb limit"
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
    parseError "string exceeds the prettyM HTML request"
  let mut bytes := ByteArray.emptyWithCapacity length
  for offset in [0:length] do
    bytes := bytes.push cursor.input[cursor.position + offset]!
  set { cursor with position := stop }
  match String.fromUTF8? bytes with
  | some string => pure string
  | none => parseError "prettyM HTML request contains invalid UTF-8"

private def beginNode : Parser Unit := do
  let cursor ← get
  if cursor.nodes >= maximumNodes then
    parseError "format exceeds the prettyM HTML node limit"
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

private def pushUInt32 (output : ByteArray) (value : Nat) : ByteArray :=
  output
    |>.push (UInt8.ofNat value)
    |>.push (UInt8.ofNat (value / 256))
    |>.push (UInt8.ofNat (value / 65536))
    |>.push (UInt8.ofNat (value / 16777216))

private def pushString (output : ByteArray) (value : String) : ByteArray := Id.run do
  let bytes := value.toUTF8
  let mut output := pushUInt32 output bytes.size
  for index in [0:bytes.size] do
    output := output.push bytes[index]!
  output

private def readBinding : Parser (Option String) := do
  match ← readByte with
  | 0 => pure none
  | 1 => pure (some (← readString))
  | _ => parseError "annotation binding flag is invalid"

private def readAnnotations : Parser (Array Pretty.TaggedAnnotation) := do
  let count ← readUInt32
  if count > maximumAnnotations then
    parseError "annotation table exceeds the prettyM HTML limit"
  let mut annotations := #[]
  for _ in [0:count] do
    let tag ← readNatural
    if annotations.any (·.tag == tag) then
      parseError "annotation table contains a duplicate tag"
    let cssClass ← readString
    let binding ← readBinding
    annotations := annotations.push { tag, annotation := { cssClass, binding } }
  pure annotations

private def readRequest : Parser
    (Std.Format × Array Pretty.TaggedAnnotation × Nat × Nat × Nat) := do
  expectByte 0x46 "magic"
  expectByte 0x50 "magic"
  expectByte 0x48 "magic"
  expectByte 0x31 "version"
  let width ← readNatural
  let indent ← readNatural
  let column ← readNatural
  let format ← readFormat
  let annotations ← readAnnotations
  let cursor ← get
  unless cursor.position == cursor.input.size do
    parseError "prettyM HTML request has trailing bytes"
  pure (format, annotations, width, indent, column)

private def responsePrefix (seed : ByteArray) (status : UInt8) : ByteArray :=
  (ByteArray.emptyWithCapacity (min seed.size 64))
    |>.push 0x46
    |>.push 0x48
    |>.push 0x52
    |>.push 0x31
    |>.push status

private def errorResponse (seed : ByteArray) (message : String) : ByteArray :=
  pushString (responsePrefix seed 1) message

private def successResponse (seed : ByteArray) (html : String) : ByteArray :=
  pushString (responsePrefix seed 0) html

/--
Bulk complete-HTML Emscripten bridge entry point.

The private wire carries the same compact `Std.Format`, sparse annotations,
and column budget used by the other browser candidates. The semantic endpoint
is the unmodified `VersoSlides.Pretty.formatHtmlForRuntime` function.
-/
@[export fir_lcnf_c_pretty_html_render_wire]
def renderWire (input : ByteArray) : ByteArray :=
  if input.size > maximumRequestBytes then
    errorResponse input "prettyM HTML request exceeds 64 MiB"
  else
    match readRequest.run { input } with
    | .error message => errorResponse input message
    | .ok ((format, annotations, width, indent, column), _) =>
        successResponse input
          (Pretty.formatHtmlForRuntime format annotations width indent column)

end Fir.LCNFC.PrettyMHtml
