import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { delimiter, dirname, join } from "node:path";

function requiredString(value, label) {
  if (typeof value !== "string" || value.length === 0) {
    throw new TypeError(`${label} must be a non-empty string`);
  }
  return value;
}

/**
 * Build only the postponed `.olean` view consumed by FIR's final-LCNF replay.
 * Native IR is deliberately not requested: a package may contain unrelated
 * declarations whose native closure is outside the selected Wasm entry.
 */
export function buildPostponedSourceView({
  lean,
  leanPath,
  moduleName,
  outputRoot,
  packageName,
  sourceFile,
}) {
  for (const [label, value] of Object.entries({
    lean, leanPath, moduleName, outputRoot, packageName, sourceFile,
  })) {
    requiredString(value, label);
  }
  if (!/^[A-Za-z0-9_.]+$/.test(moduleName)) {
    throw new TypeError("moduleName is not a canonical Lean module name");
  }

  const moduleStem = join(outputRoot, ...moduleName.split("."));
  const olean = `${moduleStem}.olean`;
  const ilean = `${moduleStem}.ilean`;
  const privateOlean = `${moduleStem}.olean.private`;
  const setup = join(outputRoot, `${moduleName}.setup.json`);
  mkdirSync(dirname(olean), { recursive: true });
  // Lean publishes interface artifacts read-only. Unlink this builder's exact
  // prior outputs before a deterministic rebuild instead of asking Lean to
  // overwrite them in place.
  for (const path of [olean, ilean, privateOlean]) {
    rmSync(path, { force: true });
  }
  const setupValue = {
    plugins: [],
    package: packageName,
    options: { "compiler.postponeCompile": true },
    name: moduleName,
    isModule: true,
    importArts: {},
    dynlibs: [],
  };
  writeFileSync(setup, `${JSON.stringify(setupValue, null, 2)}\n`);
  execFileSync(lean, [sourceFile, "-o", olean, "-i", ilean,
    "--setup", setup], {
    encoding: "utf8",
    env: { ...process.env, LEAN_PATH: leanPath },
    stdio: ["ignore", "inherit", "inherit"],
  });
  for (const path of [olean, privateOlean]) {
    if (!existsSync(path)) {
      throw new Error(`postponed source view did not produce ${path}`);
    }
  }
  return {
    moduleName,
    olean,
    privateOlean,
    leanPath: `${outputRoot}${delimiter}${leanPath}`,
  };
}
