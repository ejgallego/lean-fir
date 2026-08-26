#!/usr/bin/env node

import { existsSync } from "node:fs";

import {
  deliverMessage,
  inspectMailbox,
  mailboxProtocol,
  notifyCodexSession,
  resolveMailbox,
  terminalStates,
} from "./mailbox-lib.mjs";

function usage() {
  console.error(
    "usage: node scripts/mailbox.mjs <check|list|deliver> [DRAFT] " +
    "[--mailbox PATH] [--notify-session SESSION] [--all] [--json]",
  );
}

function parseArgs(argv) {
  const [command, ...rest] = argv;
  if (!new Set(["check", "list", "deliver"]).has(command)) {
    throw new Error("expected `check`, `list`, or `deliver`");
  }
  const options = {
    command,
    all: false,
    json: false,
    mailbox: null,
    draft: null,
    notifySession: null,
  };
  for (let index = 0; index < rest.length; index += 1) {
    const argument = rest[index];
    if (argument === "--all") options.all = true;
    else if (argument === "--json") options.json = true;
    else if (argument === "--mailbox") {
      options.mailbox = rest[index + 1];
      if (!options.mailbox || options.mailbox.startsWith("--")) {
        throw new Error("`--mailbox` requires a path");
      }
      index += 1;
    } else if (argument === "--notify-session") {
      options.notifySession = rest[index + 1];
      if (!options.notifySession || options.notifySession.startsWith("--")) {
        throw new Error("`--notify-session` requires a session UUID or exact name");
      }
      index += 1;
    } else if (command === "deliver" && !options.draft) options.draft = argument;
    else throw new Error(`unknown argument ${JSON.stringify(argument)}`);
  }
  if (command !== "list" && (options.all || options.json)) {
    throw new Error("`--all` and `--json` are list options");
  }
  if (command !== "deliver" && options.notifySession) {
    throw new Error("`--notify-session` is a deliver option");
  }
  if (command === "deliver" && !options.draft) throw new Error("deliver requires a draft path");
  return options;
}

function printWarnings(result) {
  if (result.ignoredFiles.length > 0) {
    console.warn(`warning: ignored non-message file(s): ${result.ignoredFiles.join(", ")}`);
  }
}

function check(result) {
  printWarnings(result);
  if (result.errors.length > 0) {
    for (const error of result.errors) console.error(`error: ${error}`);
    console.error(`mailbox check failed with ${result.errors.length} error(s)`);
    process.exitCode = 1;
    return;
  }
  console.log(`mailbox ok: ${result.threads.length} v1 thread(s), ${result.messages.length} message(s)`);
}

function list(result, options) {
  if (result.errors.length > 0) {
    for (const error of result.errors) console.error(`error: ${error}`);
    console.error("mailbox list requires a valid mailbox; run make mailbox-check");
    process.exitCode = 1;
    return;
  }
  const threads = result.threads.filter((thread) => options.all || !terminalStates.has(thread.state));
  if (options.json) {
    console.log(JSON.stringify({
      protocol: mailboxProtocol,
      mailbox: result.mailboxPath,
      ignoredFiles: result.ignoredFiles,
      threads,
    }, null, 2));
    return;
  }
  printWarnings(result);
  if (threads.length === 0) {
    console.log(options.all ? "no v1 mailbox threads" : "no active v1 mailbox threads");
    return;
  }
  for (const thread of threads) {
    const owner = thread.owner ? ` owner=${thread.owner}` : "";
    const disposition = thread.disposition ? ` disposition=${thread.disposition}` : "";
    console.log(`${thread.state.padEnd(11)} ${thread.threadId} ${thread.from} -> ${thread.to}${owner}${disposition}`);
    console.log(`  ${thread.subject} (${thread.messageCount} message${thread.messageCount === 1 ? "" : "s"}, tail ${thread.tail})`);
    const lane = [
      ["worktree", thread.worktree],
      ["branch", thread.branch],
      ["base", thread.base],
      ["head", thread.head],
      ["worktree-state", thread.worktreeState],
      ["publication", thread.publication],
    ].filter(([, value]) => value).map(([name, value]) => `${name}=${value}`);
    if (lane.length > 0) console.log(`  lane: ${lane.join(" ")}`);
    if (thread.integrationCheckpoint) {
      const checkpoint = thread.integrationCheckpoint;
      console.log(`  integration checkpoint: message=${checkpoint.messageId} ` +
        `head=${checkpoint.head} worktree=${checkpoint.worktree} ` +
        `branch=${checkpoint.branch} base=${checkpoint.base}`);
    }
    if (thread.parentThread) console.log(`  parent: ${thread.parentThread}`);
    if (thread.dependsOn.length > 0) console.log(`  depends on: ${thread.dependsOn.join(", ")}`);
  }
}

let options;
try {
  options = parseArgs(process.argv.slice(2));
} catch (error) {
  console.error(`error: ${error.message}`);
  usage();
  process.exit(2);
}

if (options) {
  try {
    const mailboxPath = resolveMailbox({ mailbox: options.mailbox });
    if (options.command !== "deliver" && options.mailbox && !existsSync(mailboxPath)) {
      throw new Error(`mailbox does not exist: ${mailboxPath}`);
    }
    if (options.command === "deliver") {
      const delivered = deliverMessage(mailboxPath, options.draft);
      console.log(`delivered ${delivered.messageId} -> ${delivered.destination}`);
      if (options.notifySession) {
        const notification = notifyCodexSession(options.notifySession, delivered);
        if (notification.ok) {
          console.log(`notified Codex session ${options.notifySession}`);
        } else {
          console.warn(
            `warning: durable delivery succeeded, but Codex notification failed: ${notification.detail}`,
          );
        }
      }
    } else {
      const result = inspectMailbox(mailboxPath);
      if (options.command === "check") check(result);
      else list(result, options);
    }
  } catch (error) {
    console.error(`error: ${error.message}`);
    process.exitCode = 1;
  }
}
