import assert from "node:assert/strict";
import test from "node:test";
import {
  chmodSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { buildPostponedSourceView } from "./postponed-source-view.mjs";

const valid = {
  lean: "/does/not/run",
  leanPath: "/lean/path",
  moduleName: "Client.Source",
  outputRoot: "/workspace/.deps/fir-postponed-source-view-test",
  packageName: "ClientSourceView",
  sourceFile: "/client/Source.lean",
};

test("rejects an empty required argument before invoking Lean", () => {
  assert.throws(() => buildPostponedSourceView({ ...valid, sourceFile: "" }),
    /sourceFile must be a non-empty string/);
});

test("rejects a non-canonical Lean module name before invoking Lean", () => {
  assert.throws(() => buildPostponedSourceView({
    ...valid,
    moduleName: "Client/Source",
  }), /moduleName is not a canonical Lean module name/);
});

test("rebuilds after Lean made the prior interface read-only", () => {
  const directory = dirname(fileURLToPath(import.meta.url));
  const parent = resolve(directory, "../../.deps/package-tools-tests");
  mkdirSync(parent, { recursive: true });
  const scratch = mkdtempSync(join(parent, "postponed-source-view-"));
  try {
    const fakeLean = join(scratch, "fake-lean.mjs");
    writeFileSync(fakeLean, `
      import { chmodSync, mkdirSync, writeFileSync } from "node:fs";
      import { dirname } from "node:path";
      const output = process.argv[process.argv.indexOf("-o") + 1];
      const interfaceOutput = process.argv[process.argv.indexOf("-i") + 1];
      mkdirSync(dirname(output), { recursive: true });
      writeFileSync(output, "olean\\n");
      writeFileSync(output + ".private", "private\\n");
      writeFileSync(interfaceOutput, "ilean\\n");
      chmodSync(interfaceOutput, 0o444);
    `);
    const options = {
      lean: process.execPath,
      leanPath: "/lean/path",
      moduleName: "Client.Source",
      outputRoot: join(scratch, "output"),
      packageName: "ClientSourceView",
      sourceFile: fakeLean,
    };
    buildPostponedSourceView(options);
    buildPostponedSourceView(options);
    assert.equal(readFileSync(join(options.outputRoot,
      "Client/Source.ilean"), "utf8"), "ilean\n");
  } finally {
    chmodSync(scratch, 0o700);
    rmSync(scratch, { recursive: true, force: true });
  }
});
