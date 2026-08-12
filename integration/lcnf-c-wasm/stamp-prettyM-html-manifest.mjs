import { execFileSync } from "node:child_process";
import { readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";

const [manifestArgument, firArgument, versoArgument] = process.argv.slice(2);
if (!manifestArgument || !firArgument || !versoArgument) {
  throw new Error(
    "usage: node stamp-prettyM-html-manifest.mjs <manifest> <fir-root> <verso-root>",
  );
}

function git(root, ...args) {
  return execFileSync("git", ["-C", root, ...args], { encoding: "utf8" }).trim();
}

function source(root) {
  return {
    repository: git(root, "remote", "get-url", "origin"),
    commit: git(root, "rev-parse", "HEAD"),
    dirty: git(root, "status", "--porcelain") !== "",
  };
}

const manifestPath = resolve(manifestArgument);
const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
manifest.interface = {
  browserApi: "fir.prettyM.html.emscripten.browser/v1",
  input: "lean-4.32-Std.Format.compact/v1-plus-tagged-annotations",
  wire: "fir.prettyM.html.emscripten-wire/v1",
  output: "verso-token-html/v1",
  endpoint: "escaped HTML before DOM commit",
  phases: ["encode", "execute", "decode"],
};
manifest.producer = {
  pipeline: "lean-final-lcnf-to-c-to-emscripten-html",
  fir: source(resolve(firArgument)),
  verso: source(resolve(versoArgument)),
};
await writeFile(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);
