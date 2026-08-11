import VersoSlides.Pretty

open Lean Std
open VersoSlides.Pretty

namespace VersoFirHtml.Oracle

private def tagged (tag : Nat) (cssClass : String)
    (binding : Option String := none) : TaggedAnnotation := {
  tag
  annotation := { cssClass, binding } }

private def cases : Array
    (String × Std.Format × Array TaggedAnnotation × Nat × Nat × Nat) := #[
  ("empty", Std.Format.nil, #[], 80, 0, 0),
  ("plain escape", Std.Format.text "α<&\"", #[], 80, 0, 0),
  ("annotated escape", Std.Format.tag 5 "α<&\"",
    #[tagged 5 "kw<&\"" (some "b<&\"")], 80, 0, 0),
  ("nested sparse tags", Std.Format.tag 4
    ("a" ++ Std.Format.tag 109 "β" ++ "c"),
    #[tagged 4 "outer", tagged 109 "inner" (some "bind-λ")], 80, 0, 0),
  ("missing inner annotation", Std.Format.tag 7
    ("a" ++ Std.Format.tag 8 "b"), #[tagged 7 "outer"], 80, 0, 0),
  ("multiple end tags", Std.Format.tag 17
    (Std.Format.tag 29 "x"), #[tagged 17 "a", tagged 29 "b"], 80, 0, 0),
  ("indented newline", Std.Format.nest 7
    ("a" ++ Std.Format.line ++ "b"), #[], 1, 2, 0),
  ("nonzero column", Std.Format.group
    ("hello" ++ Std.Format.line ++ "world"), #[], 10, 3, 9)]

def main : IO UInt32 := do
  for (name, format, annotations, width, indent, column) in cases do
    let html := formatHtmlForRuntime format annotations width indent column
    IO.println s!"{name}\t{(toJson html).compress}"
  return 0

end VersoFirHtml.Oracle

def main : IO UInt32 := VersoFirHtml.Oracle.main
