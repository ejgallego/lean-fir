import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

import {
  loadEmscriptenPrettyMHtmlAdapter,
  PrettyFormat as F,
} from "./prettyM-html-emscripten-adapter.mjs";

const [manifestArgument, nativePackageArgument] = process.argv.slice(2);
if (manifestArgument === undefined || nativePackageArgument === undefined) {
  throw new Error(
    "usage: node check-prettyM-html-differential.mjs " +
      "<prettyM-html.manifest.json> <FIR-native-HTML-package>",
  );
}

const nativePackage = resolve(nativePackageArgument);
const nativeModule = await import(
  pathToFileURL(join(nativePackage, "prettyM-browser-adapter.mjs"))
);
const [nativeBytes, nativeManifest, nativeBuild] = await Promise.all([
  readFile(join(nativePackage, "prettyM.wasm")),
  readFile(join(nativePackage, "prettyM.wasm.json"), "utf8").then(JSON.parse),
  readFile(join(nativePackage, "BUILD.json"), "utf8").then(JSON.parse),
]);

const [llvm, native] = await Promise.all([
  loadEmscriptenPrettyMHtmlAdapter(
    pathToFileURL(resolve(manifestArgument)),
  ),
  nativeModule.createPrettyMAdapter({
    bytes: nativeBytes,
    manifest: nativeManifest,
    build: nativeBuild,
  }),
]);

const annotation = (tag, cssClass, binding = null) => ({
  tag,
  annotation: { cssClass, binding },
});
const cases = [
  {
    name: "empty",
    request: { format: F.nil(), annotations: [], width: 80 },
  },
  {
    name: "plain escaped Unicode",
    request: { format: F.text('α<&"'), annotations: [], width: 80 },
  },
  {
    name: "annotated escape",
    request: {
      format: F.tag(5, F.text('α<&"')),
      annotations: [annotation(5, 'kw<&"', 'b<&"')],
      width: 80,
    },
  },
  {
    name: "nested sparse tags",
    request: {
      format: F.tag(
        4,
        F.append(F.text("a"), F.append(F.tag(109, F.text("β")), F.text("c"))),
      ),
      annotations: [
        annotation(4, "outer"),
        annotation(109, "inner", "bind-λ"),
      ],
      width: 80,
    },
  },
  {
    name: "missing inner annotation",
    request: {
      format: F.tag(7, F.append(F.text("a"), F.tag(8, F.text("b")))),
      annotations: [annotation(7, "outer")],
      width: 80,
    },
  },
  {
    name: "multiple end tags",
    request: {
      format: F.tag(17, F.tag(29, F.text("x"))),
      annotations: [annotation(17, "a"), annotation(29, "b")],
      width: 80,
    },
  },
  {
    name: "indented newline",
    request: {
      format: F.nest(7, F.append(F.text("a"), F.append(F.line(), F.text("b")))),
      annotations: [],
      width: 1,
      indent: 2,
      column: 0,
    },
  },
  {
    name: "nonzero column",
    request: {
      format: F.group(F.append(F.text("hello"), F.append(F.line(), F.text("world")))),
      annotations: [],
      width: 10,
      indent: 3,
      column: 9,
    },
  },
];

for (const { name, request } of cases) {
  const expected = native.render(request);
  const actual = llvm.render(request);
  assert.equal(actual.html, expected.html, `${name}: escaped HTML differs`);
  assert.ok(actual.memory.requestBytes > 0, `${name}: empty request accounting`);
  assert.ok(actual.memory.responseBytes > 0, `${name}: empty response accounting`);
}

const repeated = cases[2].request;
for (let index = 0; index < 32; index += 1) {
  assert.equal(
    llvm.render(repeated).html,
    native.render(repeated).html,
    `repeated render ${index} differs`,
  );
}

const cyclic = { kind: "group", body: undefined };
cyclic.body = cyclic;
assert.throws(
  () => llvm.render({ format: cyclic, annotations: [], width: 80 }),
  /contains a cycle/,
);
assert.throws(
  () =>
    llvm.render({
      format: F.text("bad"),
      annotations: [annotation(1, "a"), annotation(1, "b")],
      width: 80,
    }),
  /duplicate annotation tag/,
);

llvm.dispose();
console.log(
  `PASS C/Emscripten and FIR-native complete HTML agree (${cases.length} cases)`,
);
