import { execFileSync } from "node:child_process";
import { realpathSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));
const commit = execFileSync("git", ["rev-parse", "HEAD"], {
  cwd: firRoot,
  encoding: "utf8",
}).trim();
const preview = process.env.FIR_RAW_PACKAGE_PREVIEW_DIR ??
  join(firRoot, ".deps/previews",
    `lean-zip-raw-determinism-${commit.slice(0, 12)}`);

execFileSync(process.execPath, [join(directory, "package-raw.mjs"),
  "--check-determinism"], {
  cwd: directory,
  env: {
    ...process.env,
    FIR_RAW_PACKAGE_PREVIEW_DIR: preview,
  },
  stdio: "inherit",
});
