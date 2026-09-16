import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { chmodSync, existsSync, mkdirSync, readFileSync, renameSync, symlinkSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import test from "node:test";
import { makeToolingTemporaryDirectory } from "./worktree-temp.mjs";
import { prepareSource, sourceIdentity, setupIdentities } from "./source-prepare.mjs";

const commit = "6a10ac8c22beadecabdbb0919c2b50214762f91d";
function fixture() {
  const root = makeToolingTemporaryDirectory("source-prepare-test-");
  const source = join(root, "source");
  const dependency = join(root, "dep");
  const toolchainDirectory = join(root, "toolchain");
  for (const path of [source, dependency, join(toolchainDirectory, "bin")]) mkdirSync(path, { recursive: true });
  for (const tool of ["lean", "lake"]) writeFileSync(join(toolchainDirectory, "bin", tool), "fixture");
  writeFileSync(join(source, "Main.lean"), "import Dep\ndef mainValue := Dep.value\n");
  writeFileSync(join(source, "lakefile.toml"), 'name = "fixture"\n');
  writeFileSync(join(source, "lean-toolchain"), "leanprover/lean4:v4.34.0-rc2\n");
  writeFileSync(join(source, "lake-manifest.json"), JSON.stringify({ version: "1.2.0", packages: [
    { name: "dep", type: "git", url: "https://unavailable.invalid/dep", rev: "a".repeat(40), configFile: "lakefile.toml" },
  ] }));
  writeFileSync(join(dependency, "lakefile.toml"), 'name = "dep"\n');
  writeFileSync(join(dependency, "Dep.lean"), "def Dep.value := 7\n");
  const packages = join(root, "paths.json");
  writeFileSync(packages, JSON.stringify({ dep: "dep" }));
  return { root, dependency, options: { source, packages, toolchainDirectory, leanCommit: commit, modules: ["Main"], entries: ["mainValue"] } };
}
function fakeLake(action = () => {}) {
  return (command, args, context) => {
    assert(existsSync(context.env.TMPDIR), "TMPDIR must exist before even toolchain verification");
    if (command.endsWith("/lean")) return { status: 0, stdout: `Lean 4.34.0-rc2, commit ${commit}`, stderr: "" };
    assert(args.some((arg) => arg.startsWith("--packages=")));
    assert(args.includes("+Main:setup"));
    assert.equal(context.env.LAKE_ARTIFACT_CACHE, "false");
    const artifact = join(context.cwd, ".lake", "build", "Main.olean");
    mkdirSync(join(context.cwd, ".lake", "build"), { recursive: true });
    writeFileSync(artifact, "private artifact");
    const outcome = action(command, args, context);
    return outcome ?? { status: 0, stdout: JSON.stringify({ name: "Main", importArts: { Main: [artifact] }, plugins: [{ path: artifact }] }), stderr: "" };
  };
}

test("supplied paths relocate, original authority is unchanged, setups record consumed bytes", () => {
  const { options } = fixture();
  const before = sourceIdentity(options.source);
  const result = prepareSource(options, fakeLake());
  assert.deepEqual(sourceIdentity(options.source), before);
  assert.deepEqual(sourceIdentity(result.project), before);
  const mapped = JSON.parse(readFileSync(result.packages.path));
  assert.equal(mapped.packages[0].type, "path");
  assert(!Object.hasOwn(mapped.packages[0], "url"));
  assert(mapped.packages[0].dir.startsWith(result.workspace));
  assert.equal(result.setups[0].artifacts.length, 1);
  assert.equal(result.setups[0].plugins.length, 1);
  assert.equal(result.setups[0].artifacts[0].byteLength, 16);
  assert(existsSync(join(result.workspace, "PREPARED.json")));
});
test("relocated input directory and relative map remain usable", () => {
  const input = fixture();
  const moved = `${input.root}-relocated`;
  renameSync(input.root, moved);
  for (const key of ["source", "packages", "toolchainDirectory"]) input.options[key] = input.options[key].replace(input.root, moved);
  assert(prepareSource(input.options, fakeLake()).project);
});
test("missing supplied dependency fails before Lake can fetch it", () => {
  const { options } = fixture();
  writeFileSync(options.packages, "{}");
  let lakeCalls = 0;
  assert.throws(() => prepareSource(options, fakeLake(() => { lakeCalls++; })), /missing supplied dependency: dep/);
  assert.equal(lakeCalls, 0);
});
test("wrong exact toolchain is rejected", () => {
  const { options } = fixture();
  assert.throws(() => prepareSource(options, () => ({ status: 0, stdout: "Lean wrong version" })), /Lean commit mismatch/);
});
test("private and supplied source mutation are rejected even when the child succeeds", () => {
  for (const supplied of [false, true]) {
    const { options } = fixture();
    assert.throws(() => prepareSource(options, fakeLake((_command, _args, context) => {
      writeFileSync(join(supplied ? options.source : context.cwd, "Main.lean"), "changed\n");
    })), /source mutated/);
  }
});
test("supplied and derived path-map mutations cannot change preparation authority", () => {
  for (const supplied of [false, true]) {
    const { options } = fixture();
    assert.throws(() => prepareSource(options, fakeLake((_command, args) => {
      const path = supplied ? options.packages : args.find((arg) => arg.startsWith("--packages=")).slice("--packages=".length);
      writeFileSync(path, "{}\n");
    })), /dependency path map mutated/);
  }
});
test("real child failure status and complete failure output are retained", () => {
  const { options } = fixture();
  let error;
  try { prepareSource(options, fakeLake(() => ({ status: 23, stdout: "full stdout\n", stderr: "full stderr\n" }))); }
  catch (caught) { error = caught; }
  assert.equal(error.exitCode, 23);
  const log = error.message.split("full log: ")[1];
  assert.match(readFileSync(log, "utf8"), /full stdout\nfull stderr/);
});
test("signal termination propagates the conventional nonzero shell status", () => {
  const { options } = fixture();
  assert.throws(() => prepareSource(options, fakeLake(() => ({ status: null, signal: "SIGTERM", stdout: "terminated" }))),
    (error) => error.exitCode === 143 && error.message.includes("SIGTERM"));
});
test("Git rematerialization is rejected with 125 and cannot be hidden by a successful Lake child", () => {
  const { options } = fixture();
  assert.throws(() => prepareSource(options, fakeLake((_command, _args, context) => {
    const git = join(context.env.PATH.split(":")[0], "git");
    for (const args of [["clone", "unavailable", "new"], ["fetch"], ["pull"], ["submodule", "update"]]) {
      const child = spawnSync(git, args, { ...context, encoding: "utf8" });
      assert.equal(child.status, 125);
    }
  })), /Git mutation\/rematerialization attempted/);
});
test("setup artifacts outside supplied workspace/toolchain are rejected", () => {
  const { options } = fixture();
  const outside = join(options.source, "Main.lean");
  assert.throws(() => setupIdentities({ importArts: { Main: [outside] } }, options.source, [options.toolchainDirectory]), /unsupplied artifact/);
});
test("transitive missing dependencies cannot fall through to Git materialization", () => {
  const { options, dependency } = fixture();
  writeFileSync(join(dependency, "lake-manifest.json"), JSON.stringify({ version: "1.2.0", packages: [{ name: "transitive", type: "git" }] }));
  assert.throws(() => prepareSource(options, fakeLake()), /missing supplied dependency: transitive/);
});
test("non-path dependency values and unused inputs are rejected", () => {
  const { options, dependency } = fixture();
  writeFileSync(options.packages, JSON.stringify({ dep: { dir: dependency } }));
  assert.throws(() => prepareSource(options, fakeLake()), /paths only/);
  writeFileSync(options.packages, JSON.stringify({ dep: dependency, unused: dependency }));
  assert.throws(() => prepareSource(options, fakeLake()), /unused packages/);
});
test("source symlinks cannot smuggle unsupplied input bytes", () => {
  const { options, dependency } = fixture();
  symlinkSync(join(dependency, "Dep.lean"), join(options.source, "Linked.lean"));
  assert.throws(() => prepareSource(options, fakeLake()), /source symlink is unsupported/);
});
test("public command exits with the actual failing Lake status, quietly retaining both output streams", () => {
  const { options } = fixture();
  const lean = join(options.toolchainDirectory, "bin", "lean");
  const lake = join(options.toolchainDirectory, "bin", "lake");
  writeFileSync(lean, `#!/usr/bin/env node\nconsole.log(${JSON.stringify(`Lean 4.34.0-rc2 commit ${commit}`)});\n`);
  writeFileSync(lake, '#!/usr/bin/env node\nconsole.log("retained stdout");console.error("retained stderr");process.exitCode=23;\n');
  chmodSync(lean, 0o700);
  chmodSync(lake, 0o700);
  const cli = new URL("./source-prepare.mjs", import.meta.url);
  const child = spawnSync(process.execPath, [cli.pathname, "--toolchain-dir", options.toolchainDirectory,
    "--lean-commit", commit, "--source", options.source, "--packages", options.packages, "--module", "Main"], { encoding: "utf8" });
  assert.equal(child.status, 23);
  assert.equal(child.stdout, "");
  assert.match(child.stderr, /^FAIL source-prepare:/);
  assert(!child.stderr.includes("retained stdout"));
  const log = child.stderr.trim().split("full log: ")[1];
  assert.match(readFileSync(log, "utf8"), /retained stdout\nretained stderr/);
});
