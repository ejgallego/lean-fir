import VersoBlueprint.PreviewManifest

/-! Compatibility for two consolidated multi-page sections. Native section
lookup owns the destination; these documents preserve their former public
paths without adding reading stops to the table of contents. -/

namespace FirBlueprint.Compatibility

open Informal.PreviewManifest

private def redirects : Array (String × String × String) := #[
  ("Formal-reference-catalog-_LPAR_W6_RPAR_/Source-and-graph-reading-boundaries",
    "../../find/?domain=Verso.Genre.Manual.section&name=w6-source-boundary",
    "Reading this catalog"),
  ("Source-and-evidence-boundaries",
    "../find/?domain=Verso.Genre.Manual.section&name=documentation-migration",
    "Reading source evidence")]

private def document (target title : String) : String :=
  let target := target.replace "&" "&amp;"
  "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
    s!"<title>{title}</title>\n<meta http-equiv=\"refresh\" content=\"0; url={target}\">\n" ++
    s!"</head>\n<body><p>This section has moved to <a href=\"{target}\">{title}</a>.</p></body>\n</html>\n"

/-- Emit only former multi-page paths, after native pages and section lookup. -/
def emit : BlueprintExtraStep := fun prepared => do
  match prepared.mode with
  | .single => pure ()
  | .multi =>
    let output := prepared.config.destination / "html-multi"
    for (route, target, title) in redirects do
      -- Current native pages win. Files from an older build at these two
      -- reserved paths can be replaced, so upgrading needs no manual cleanup.
      if prepared.state.externalTags.toArray.any (fun (_, link) =>
          link.path.relativeLink == route ++ "/") then
        throw <| IO.userError s!"compatibility redirect collides with a current native page: {route}"
      let directory := output / route
      let path := directory / "index.html"
      IO.FS.createDirAll directory
      IO.FS.writeFile path (document target title)

end FirBlueprint.Compatibility
