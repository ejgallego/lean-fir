import VersoSlides.Pretty

open Lean Std
open VersoSlides.Pretty

namespace VersoFirFlat.Oracle

private def balanced : Nat → Std.Format
  | 0 => Std.Format.text "λ"
  | n + 1 =>
      let child := balanced n
      child ++ child

private def cases : Array (String × Std.Format × Nat × Nat × Nat) := #[
  ("empty", Std.Format.nil, 80, 0, 0),
  ("nested tags", Std.Format.tag 4
    ("α" ++ Std.Format.tag 9 ("b" ++ Std.Format.line ++ "γ")), 3, 0, 0),
  ("multiple end tags", Std.Format.tag 17 (Std.Format.tag 29 "x"), 80, 0, 0),
  ("indented newline", Std.Format.nest 7
    ("a" ++ Std.Format.line ++ "b"), 1, 2, 0),
  ("nonzero column wide", Std.Format.group
    ("hello" ++ Std.Format.line ++ "world"), 20, 3, 9),
  ("nonzero column narrow", Std.Format.group
    ("hello" ++ Std.Format.line ++ "world"), 10, 3, 9),
  ("large tag", Std.Format.tag 1099511627779 "payload", 80, 0, 0),
  ("balanced append", balanced 10, 80, 0, 0),
  ("unicode chunk", Std.Format.tag 3
    (Std.Format.text (String.Internal.pushn "" 'α' 131072)), 200000, 0, 0)]

def main : IO UInt32 := do
  for (name, format, width, indent, column) in cases do
    let rendered := formatRenderedForRuntime format width indent column
    IO.println s!"{name}\t{(toJson rendered).compress}"
  return 0

end VersoFirFlat.Oracle

def main : IO UInt32 := VersoFirFlat.Oracle.main
