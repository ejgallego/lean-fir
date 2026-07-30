import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

import {
  loadEmscriptenPrettyMAdapter,
  PrettyFormat as F,
} from "./prettyM-emscripten-adapter.mjs";

function fail(message) {
  throw new Error(`prettyM differential check: ${message}`);
}

const [emscriptenManifestArgument, firPackageArgument] = process.argv.slice(2);
if (emscriptenManifestArgument === undefined || firPackageArgument === undefined) {
  fail(
    "usage: node check-prettyM-differential.mjs " +
      "<prettyM.manifest.json> <FIR-native-package-directory>",
  );
}

const emscriptenManifest = pathToFileURL(resolve(emscriptenManifestArgument));
const firPackage = resolve(firPackageArgument);
const firAdapterModule = await import(
  pathToFileURL(join(firPackage, "prettyM-browser-adapter.mjs"))
);
const [firBytes, firManifest, firBuild] = await Promise.all([
  readFile(join(firPackage, "prettyM.wasm")),
  readFile(join(firPackage, "prettyM.wasm.json"), "utf8").then(JSON.parse),
  readFile(join(firPackage, "BUILD.json"), "utf8").then(JSON.parse),
]);

const [emscripten, firNative] = await Promise.all([
  loadEmscriptenPrettyMAdapter(emscriptenManifest),
  firAdapterModule.createPrettyMAdapter({
    bytes: firBytes,
    manifest: firManifest,
    build: firBuild,
  }),
]);

const malformed = Uint8Array.of(0xff);
const malformedPointer =
  emscripten.exports.fir_lcnf_c_pretty_input_alloc(malformed.length) >>> 0;
assert.notEqual(malformedPointer, 0, "could not allocate malformed request");
emscripten.module.HEAPU8.set(malformed, malformedPointer);
assert.equal(
  emscripten.exports.fir_lcnf_c_pretty_render(malformed.length) >>> 0,
  0,
  "C bridge rejected a protocol-level error response",
);
const malformedResultPointer =
  emscripten.exports.fir_lcnf_c_pretty_result_ptr() >>> 0;
const malformedResultLength =
  emscripten.exports.fir_lcnf_c_pretty_result_len() >>> 0;
assert.ok(malformedResultLength > 5, "protocol error response is truncated");
assert.deepEqual(
  Array.from(emscripten.module.HEAPU8.slice(
    malformedResultPointer,
    malformedResultPointer + 5,
  )),
  [0x46, 0x50, 0x52, 0x31, 1],
  "malformed request did not produce a versioned protocol error",
);

function coverageFormat() {
  return F.append(
    F.append(
      F.append(
        F.nil(),
        F.tag(7, F.group(F.append(
          F.append(F.text("α"), F.line()),
          F.text("β"),
        ))),
      ),
      F.line(),
    ),
    F.nest(2, F.append(
      F.append(
        F.append(
          F.append(F.text("."), F.align(false)),
          F.text("γ"),
        ),
        F.line(),
      ),
      F.text("δ\nε"),
    )),
  );
}

const hugeNumeric = (1n << 130n) + 17n;
const largeText = "λ".repeat(512 * 1024);
const requests = [
  {
    name: "styled Unicode coverage",
    request: { format: coverageFormat(), width: 80 },
  },
  {
    name: "narrow all-or-none group",
    request: {
      format: F.group(F.append(
        F.text("left"),
        F.append(F.line(), F.text("right")),
      )),
      width: 5,
      indent: 1,
      column: 0,
    },
  },
  {
    name: "fill group",
    request: {
      format: F.group(F.append(
        F.text("a"),
        F.append(F.line(), F.append(
          F.text("bb"),
          F.append(F.line(), F.text("ccc")),
        )),
      ), "fill"),
      width: 5,
      indent: 0,
      column: 0,
    },
  },
  {
    name: "arbitrary-precision tag and signed nests",
    request: {
      format: F.append(
        F.tag(hugeNumeric, F.text("tag")),
        F.append(
          F.nest(hugeNumeric, F.text("+")),
          F.nest(-hugeNumeric, F.text("-")),
        ),
      ),
      width: hugeNumeric,
    },
  },
  {
    name: "nonzero initial indent and column",
    request: {
      format: F.append(F.align(false), F.append(F.line(), F.text("tail"))),
      width: "12",
      indent: 3n,
      column: 4,
    },
  },
  {
    name: "one-MiB UTF-8 bulk transfer",
    request: {
      format: F.tag(hugeNumeric, F.text(largeText)),
      width: hugeNumeric,
    },
  },
];

for (const { name, request } of requests) {
  const firResult = firNative.render(request);
  const emscriptenResult = emscripten.render(request);
  assert.deepEqual(
    emscriptenResult.trace,
    firResult.trace,
    `${name}: C/Emscripten and FIR-native traces differ`,
  );
  assert.ok(
    emscriptenResult.memory.requestBytes > 0 &&
      emscriptenResult.memory.responseBytes > 0,
    `${name}: C/Emscripten wire accounting is empty`,
  );
}

for (let index = 0; index < 8; index += 1) {
  const request = {
    format: F.tag(hugeNumeric + BigInt(index), F.text(`repeat-${index}`)),
    width: 80,
  };
  assert.deepEqual(
    emscripten.render(request).trace,
    firNative.render(request).trace,
    `repeated render ${index}: traces differ`,
  );
}

const cyclic = { kind: "group", body: undefined };
cyclic.body = cyclic;
assert.throws(
  () => emscripten.render({ format: cyclic, width: 80 }),
  /contains a cycle/,
);
assert.throws(
  () => firNative.render({ format: cyclic, width: 80 }),
  /contains a cycle/,
);

emscripten.dispose();
console.log(
  "PASS C/Emscripten and FIR-native prettyM facades agree on exact traces",
);
