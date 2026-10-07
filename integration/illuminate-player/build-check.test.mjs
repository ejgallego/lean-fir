import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  copyFileSync, mkdirSync, mkdtempSync, readFileSync, readlinkSync, rmSync,
  symlinkSync, writeFileSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";

const directory = dirname(fileURLToPath(import.meta.url));
const toolchain = readFileSync(join(directory, "lean-toolchain"), "utf8");
const source = readFileSync(join(directory, "illuminate-source.json"), "utf8");

// These tests exercise real shell/export control flow with stubbed compilers.
// Wasm capabilities and semantics remain covered by the real recipe check.
function withFixture(run) {
  const scratch = join(directory, "../../.deps/tmp/player-build-test");
  mkdirSync(scratch, { recursive: true });
  const root = mkdtempSync(join(scratch, "commands-"));
  try {
    const recipe = join(root, "integration/illuminate-player");
    const bin = join(root, "bin");
    const illuminate = join(root, "illuminate");
    const tools = join(root, "integration/package-tools");
    for (const path of [recipe, bin, illuminate, tools, join(root, "scripts"),
      join(root, ".deps/lcnf-c-wasm/emsdk/upstream/bin")]) {
      mkdirSync(path, { recursive: true });
    }
    writeFileSync(join(root, "lean-toolchain"), toolchain);
    writeFileSync(join(recipe, "lean-toolchain"), toolchain);
    writeFileSync(join(recipe, "illuminate-source.json"), source);
    for (const name of ["build.sh", "check.sh", "export-v3-package.sh",
      "export-selection-package.mjs", "selection-package-policy.mjs",
      "illuminate-selection-player-browser-adapter.mjs"]) {
      copyFileSync(join(directory, name), join(recipe, name));
    }
    for (const name of ["verified-package.mjs", "immutable-package.mjs",
      "source-package.mjs"]) {
      copyFileSync(join(directory, "../package-tools", name), join(tools, name));
    }
    writeFileSync(join(root, "scripts/fir-lake-cache-path.sh"),
      'printf "%s\\n" "$TEST_ROOT/cache"\n');
    writeFileSync(join(root, ".deps/lcnf-c-wasm/emsdk/upstream/bin/wasm-opt"),
      "#!/usr/bin/env bash\nexit 0\n", { mode: 0o755 });
    const mock = `#!${process.execPath}
import { appendFileSync, mkdirSync, readFileSync, rmSync,
  symlinkSync, writeFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { basename, join } from "node:path";
const tool = basename(process.argv[1]);
const args = process.argv.slice(2);
const root = process.env.TEST_ROOT;
const recipe = join(root, "integration/illuminate-player");
if (tool === "git") {
  const checkout = args[1];
  if (args.includes("--show-toplevel")) process.stdout.write(checkout);
  else if (args.includes("HEAD")) process.stdout.write(
    JSON.parse(readFileSync(join(recipe, "illuminate-source.json"))).revision);
  else if (!args.includes("--porcelain")) throw Error("unexpected git command");
  process.exit(0);
}
if (tool === "node" && args[0] === "-e") {
  process.stdout.write(execFileSync(${JSON.stringify(process.execPath)}, args));
  process.exit(0);
}
const step = tool + " " + args.join(" ");
appendFileSync(join(root, "commands.jsonl"), JSON.stringify({
  step, cwd: process.cwd(), scratch: process.env.TMPDIR,
  source: process.env.ILLUMINATE_ROOT,
}) + "\\n");
const history = readFileSync(join(root, "commands.jsonl"), "utf8")
  .trim().split("\\n").map(JSON.parse);
const count = history.filter(item => item.step === step).length;
if (process.env.FAIL_STEP === args[0] ||
  process.env.FAIL_STEP === args[0] + "#" + count) process.exit(23);
if (tool === "node" && ["package.mjs", "selection-package.mjs"].includes(args[0])) {
  const name = args[0] === "package.mjs" ? "illuminate-player" :
    "illuminate-selection-player";
  const identity = process.env.CHANGE_ON_REBUILD === args[0] ? count : 1;
  const output = join(recipe, "_build", name + "-packages", "built-" + identity);
  mkdirSync(output, { recursive: true });
  const files = ["BUILD.json", name + ".wasm", name + ".wasm.json",
    name + "-browser-adapter.mjs", "smoke.mjs"];
  for (const file of files) writeFileSync(join(output, file), "fresh " + file + "\\n");
  writeFileSync(join(output, "SHA256SUMS"), files.map(file =>
    createHash("sha256").update(readFileSync(join(output, file))).digest("hex") +
      "  " + file).join("\\n") + "\\n");
  const current = join(recipe, "_build", name + "-current");
  rmSync(current, { force: true });
  symlinkSync(output, current);
}
`;
    for (const name of ["node", "lake", "git"]) {
      writeFileSync(join(bin, name), mock, { mode: 0o755 });
    }
    const environment = {
      ...process.env,
      PATH: `${bin}:${process.env.PATH}`,
      ILLUMINATE_ROOT: illuminate,
      LEAN_TOOLCHAIN: toolchain.trim(),
      TEST_ROOT: root,
      FAIL_STEP: "",
      CHANGE_ON_REBUILD: "",
    };
    const commands = () => {
      const path = join(root, "commands.jsonl");
      try {
        return readFileSync(path, "utf8").trim().split("\n").map(JSON.parse);
      } catch (error) {
        if (error.code === "ENOENT") return [];
        throw error;
      }
    };
    const execute = (name, overrides = {}, args = []) => execFileSync("bash",
      [join(recipe, name), ...args], {
        env: { ...environment, ...overrides }, stdio: ["ignore", "pipe", "pipe"],
      });
    const stale = () => {
      for (const name of ["illuminate-player", "illuminate-selection-player"]) {
        const previous = join(recipe, "_build", name + "-packages", "stale");
        mkdirSync(previous, { recursive: true });
        symlinkSync(previous, join(recipe, "_build", name + "-current"));
      }
    };
    run({ root, recipe, environment, commands, execute, stale });
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

test("build constructs both packages even when current pointers already exist", () =>
  withFixture(({ root, environment, commands, execute, stale }) => {
    stale();
    execute("build.sh");
    assert.deepEqual(commands().map(({ step }) => step),
      ["node package.mjs", "node selection-package.mjs"]);
    for (const command of commands()) {
      assert.equal(command.scratch, join(root, ".deps/tmp/illuminate-player"));
      assert.equal(command.source, environment.ILLUMINATE_ROOT);
    }
  }));

test("explicit targets construct only their selected packages", () => {
  for (const [target, expected, unrelatedFailure] of [
    ["all", ["node package.mjs", "node selection-package.mjs"], ""],
    ["full", ["node package.mjs"], "selection-package.mjs"],
    ["selection", ["node selection-package.mjs"], "package.mjs"],
  ]) {
    withFixture(({ recipe, commands, execute, stale }) => {
      stale();
      execute("build.sh", { FAIL_STEP: unrelatedFailure }, [target]);
      assert.deepEqual(commands().map(({ step }) => step), expected);
      if (target !== "all") {
        const unchanged = target === "full" ? "illuminate-selection-player" :
          "illuminate-player";
        assert.equal(readlinkSync(join(recipe, "_build", unchanged + "-current")),
          join(recipe, "_build", unchanged + "-packages", "stale"));
      }
    });
  }
});

test("invalid or extra build arguments fail before source or tool lookup", () => {
  for (const args of [["unknown"], [""], ["--full"], ["full", "selection"],
    ["--help", "extra"]]) {
    withFixture(({ root, commands, execute }) => {
      assert.throws(() => execute("build.sh", {
        ILLUMINATE_ROOT: join(root, "missing-source"),
        LEAN_TOOLCHAIN: "leanprover/lean4:v0.0.0",
      }, args), (error) => error.status === 2 &&
        error.stderr.includes("usage: build.sh [all|full|selection]"));
      assert.deepEqual(commands(), []);
    });
  }
});

test("build help requires neither source nor toolchain setup", () =>
  withFixture(({ root, commands, execute }) => {
    const output = execute("build.sh", {
      ILLUMINATE_ROOT: join(root, "missing-source"),
      LEAN_TOOLCHAIN: "leanprover/lean4:v0.0.0",
    }, ["--help"]);
    assert.match(output.toString(), /usage: build.sh \[all\|full\|selection\]/);
    assert.deepEqual(commands(), []);
  }));

test("selected builds propagate failures without consuming stale packages", () => {
  for (const [target, failure] of [["full", "package.mjs"],
    ["selection", "selection-package.mjs"]]) {
    withFixture(({ commands, execute, stale }) => {
      stale();
      assert.throws(() => execute("build.sh", { FAIL_STEP: failure }, [target]),
        (error) => error.status === 23);
      assert.deepEqual(commands().map(({ step }) => step), [`node ${failure}`]);
    });
  }
});

test("build propagates publisher failures instead of using stale pointers", () => {
  for (const [failure, expected] of [
    ["package.mjs", ["node package.mjs"]],
    ["selection-package.mjs", ["node package.mjs", "node selection-package.mjs"]],
  ]) {
    withFixture(({ commands, execute, stale }) => {
      stale();
      assert.throws(() => execute("build.sh", { FAIL_STEP: failure }),
        (error) => error.status === 23);
      assert.deepEqual(commands().map(({ step }) => step), expected);
    });
  }
});

test("check retains native, semantic, repeat-build and packaged tests in order", () =>
  withFixture(({ commands, execute }) => {
    execute("check.sh");
    const steps = commands().map(({ step }) => step);
    assert.deepEqual(steps.slice(0, 3), ["node package.mjs", "node selection-package.mjs",
      "node --test export-selection-package.test.mjs build-check.test.mjs"]);
    assert.equal(steps[3], "node check-native-capture.mjs");
    assert.match(steps[4], /lake .* build IlluminateFirNative.Examples IlluminateFirNative.SelectionExamples$/);
    assert.deepEqual(steps.slice(5), ["node smoke.mjs", "node selection-smoke.mjs",
      "node check-player-traces.mjs", "node package.mjs", "node selection-package.mjs",
      "node smoke.mjs", "node smoke.mjs"]);
    assert.notEqual(commands().at(-1).cwd, commands()[5].cwd);
  }));

test("check stops on unit, native-oracle, trace and repeat-build failures", () => {
  for (const failure of ["--test", "check-native-capture.mjs", "--keep-toolchain", "check-player-traces.mjs",
    "package.mjs#2"]) {
    withFixture(({ commands, execute }) => {
      assert.throws(() => execute("check.sh", { FAIL_STEP: failure }),
        (error) => error.status === 23);
      assert(!commands().at(-1).cwd.includes("-packages/"));
    });
  }
});

test("check rejects changed repeat-build package identities", () =>
  withFixture(({ execute }) => {
    assert.throws(() => execute("check.sh", { CHANGE_ON_REBUILD: "selection-package.mjs" }),
      (error) => error.status === 1);
  }));

test("full exporter builds once, copies and smokes without running the test campaign", () =>
  withFixture(({ root, recipe, environment, commands }) => {
    const output = join(root, "export");
    execFileSync("bash", [join(recipe, "export-v3-package.sh"), output], {
      env: environment, stdio: ["ignore", "pipe", "pipe"],
    });
    assert.deepEqual(commands().map(({ step }) => step),
      ["node package.mjs", "node smoke.mjs"]);
    assert.equal(commands().at(-1).cwd, output);
    assert.equal(readFileSync(join(output, "illuminate-player.wasm"), "utf8"),
      "fresh illuminate-player.wasm\n");
  }));

test("both exporters refuse stale packages when the build fails", () => {
  for (const kind of ["full", "selection"]) {
    withFixture(({ root, recipe, environment, commands, stale }) => {
      stale();
      const output = join(root, "export");
      const invocation = kind === "full"
        ? ["bash", [join(recipe, "export-v3-package.sh"), output]]
        : [process.execPath, [join(recipe, "export-selection-package.mjs"),
          "--output", output, "--checkout", `producer=${root}`,
          "--checkout", `illuminate=${environment.ILLUMINATE_ROOT}`]];
      const failure = kind === "full" ? "package.mjs" : "selection-package.mjs";
      assert.throws(() => execFileSync(...invocation, {
        env: { ...environment, FAIL_STEP: failure },
        stdio: ["ignore", "pipe", "pipe"],
      }), (error) => error.status === (kind === "full" ? 23 : 1));
      assert.deepEqual(commands().map(({ step }) => step), [`node ${failure}`]);
      assert.throws(() => readFileSync(join(output, "BUILD.json")),
        { code: "ENOENT" });
    });
  }
});
