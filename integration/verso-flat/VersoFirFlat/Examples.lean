import VersoSlides.Pretty

namespace VersoFirFlat.Examples

open Lean Std
open VersoSlides.Pretty

private def taggedUnicode : Rendered :=
  formatRenderedForRuntime (Std.Format.tag 5 "α") 80 0 0

#guard taggedUnicode.text == "α"
#guard taggedUnicode.events == #[
  { offset := 0, kind := 0, value := 5 },
  { offset := 2, kind := 1, value := 1 }]

private def indentedBreak : Rendered :=
  formatRenderedForRuntime
    (Std.Format.nest 3 ("a" ++ Std.Format.line ++ "b")) 1 0 0

#guard indentedBreak.text == "a\n   b"
#guard indentedBreak.events == #[
  { offset := 1, kind := 2, value := 3 }]

private def columnSensitive : Std.Format :=
  Std.Format.group ("hello" ++ Std.Format.line ++ "world")

#guard (formatRenderedForRuntime columnSensitive 20 3 9).text ==
  "hello world"
#guard (formatRenderedForRuntime columnSensitive 10 3 9).text ==
  "hello\n   world"

end VersoFirFlat.Examples
