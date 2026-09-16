import { spawnSync } from "node:child_process";
import { appendFileSync } from "node:fs";
const args = process.argv.slice(2);
let i = 0;
while (args[i] === "-C") i += 2;
const allowed = new Set(["--version", "rev-parse", "show", "status", "diff", "ls-files", "cat-file"]);
if (!allowed.has(args[i])) {
  appendFileSync(process.env.FIR_SOURCE_PREPARE_GIT_LOG, `${JSON.stringify(args)}\n`);
  console.error("source-prepare rejects Git mutation/rematerialization");
  process.exitCode = 125;
} else {
  const child = spawnSync("/usr/bin/git", args, { stdio: "inherit" });
  process.exitCode = child.status ?? 1;
}
