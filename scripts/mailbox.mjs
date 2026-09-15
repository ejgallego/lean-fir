#!/usr/bin/env node

import { existsSync } from "node:fs";

import {
  bindCodexRoute,
  deliverMessage,
  inspectMailbox,
  isMailboxAddress,
  mailboxProtocol,
  mailboxStates,
  notifyCodexSession,
  readCodexRoutes,
  resolveCodexRoute,
  resolveMailbox,
  unbindCodexRoute,
} from "./mailbox-lib.mjs";

const defaultListStates = new Set(["open", "claimed", "in-progress", "blocked"]);

function usage(print = console.error) {
  print([
    "usage:",
    "  scripts/mailbox list [--for ADDRESS] [--state STATE] " +
      "[--verbose|--json] [--all] [--mailbox PATH]",
    "  scripts/mailbox brief MESSAGE-ID [--mailbox PATH]",
    "  scripts/mailbox check [--mailbox PATH]",
    "  scripts/mailbox deliver DRAFT [--no-notify|--notify-session SESSION] " +
      "[--mailbox PATH]",
    "  scripts/mailbox route bind ADDRESS SESSION [--mailbox PATH]",
    "  scripts/mailbox route unbind ADDRESS [--mailbox PATH]",
    "  scripts/mailbox route list [--json] [--mailbox PATH]",
    "",
    "deliver resolves the recipient route and queues by default; --no-notify skips it.",
  ].join("\n"));
}

function parseArgs(argv) {
  const [command, ...arguments_] = argv;
  if (!new Set(["brief", "check", "list", "deliver", "route"]).has(command)) {
    throw new Error("expected `brief`, `check`, `list`, `deliver`, or `route`");
  }
  const rest = [...arguments_];
  const routeAction = command === "route" ? rest.shift() : null;
  if (command === "route" && !new Set(["bind", "unbind", "list"]).has(routeAction)) {
    throw new Error("route expects `bind`, `unbind`, or `list`");
  }
  const options = {
    command,
    routeAction,
    all: false,
    json: false,
    verbose: false,
    mailbox: null,
    draft: null,
    noNotify: false,
    notifySession: null,
    address: null,
    routeAddress: null,
    routeSession: null,
    messageId: null,
    states: new Set(),
  };
  for (let index = 0; index < rest.length; index += 1) {
    const argument = rest[index];
    if (argument === "--all") options.all = true;
    else if (argument === "--json") options.json = true;
    else if (argument === "--verbose") options.verbose = true;
    else if (argument === "--for") {
      options.address = rest[index + 1];
      if (!options.address || options.address.startsWith("--")) {
        throw new Error("`--for` requires an address");
      }
      if (!isMailboxAddress(options.address)) {
        throw new Error(`invalid mailbox address ${JSON.stringify(options.address)}`);
      }
      index += 1;
    } else if (argument === "--state") {
      const state = rest[index + 1];
      if (!state || state.startsWith("--")) throw new Error("`--state` requires a state");
      if (!mailboxStates.has(state)) {
        throw new Error(`unknown mailbox state ${JSON.stringify(state)}`);
      }
      options.states.add(state);
      index += 1;
    } else if (argument === "--mailbox") {
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
    } else if (argument === "--no-notify") {
      options.noNotify = true;
    } else if (command === "brief" && !options.messageId) options.messageId = argument;
    else if (command === "deliver" && !options.draft) options.draft = argument;
    else if (command === "route" && routeAction !== "list" && !options.routeAddress) {
      options.routeAddress = argument;
    } else if (command === "route" && routeAction === "bind" && !options.routeSession) {
      options.routeSession = argument;
    }
    else throw new Error(`unknown argument ${JSON.stringify(argument)}`);
  }
  const hasListOption = options.all || options.json || options.verbose ||
    options.address || options.states.size > 0;
  const routeList = command === "route" && routeAction === "list";
  if (command !== "list" && !(routeList && options.json) && hasListOption) {
    throw new Error("`--all`, `--json`, `--verbose`, `--for`, and `--state` are list options");
  }
  if (options.all && options.states.size > 0) {
    throw new Error("`--all` and `--state` cannot be combined");
  }
  if (options.json && options.verbose) {
    throw new Error("`--json` and `--verbose` cannot be combined");
  }
  if (command !== "deliver" && (options.notifySession || options.noNotify)) {
    throw new Error("`--notify-session` and `--no-notify` are deliver options");
  }
  if (options.notifySession && options.noNotify) {
    throw new Error("`--notify-session` and `--no-notify` cannot be combined");
  }
  if (command === "deliver" && !options.draft) throw new Error("deliver requires a draft path");
  if (command === "brief" && !options.messageId) throw new Error("brief requires a message ID");
  if (options.messageId && !/^[A-Z][A-Z0-9]*-[A-Z][A-Z0-9]*-[0-9]{8}-[0-9]{3}$/.test(options.messageId)) {
    throw new Error(`invalid mailbox message ID ${JSON.stringify(options.messageId)}`);
  }
  if (command === "route" && routeAction !== "list" && !options.routeAddress) {
    throw new Error(`route ${routeAction} requires an address`);
  }
  if (options.routeAddress && !isMailboxAddress(options.routeAddress)) {
    throw new Error(`invalid mailbox address ${JSON.stringify(options.routeAddress)}`);
  }
  if (command === "route" && routeAction === "bind" && !options.routeSession) {
    throw new Error("route bind requires a session UUID or exact name");
  }
  return options;
}

function compactText(text, limit = 240) {
  const normalized = text
    .replace(/```[\s\S]*?```/g, "[code omitted]")
    .replace(/^\s*[-*]\s+/gm, "")
    .replace(/\s+/g, " ")
    .trim();
  return normalized.length <= limit ? normalized : `${normalized.slice(0, limit - 1)}…`;
}

function sections(body) {
  const headings = [...body.matchAll(/^##\s+(.+?)\s*$/gm)];
  return headings.map((heading, index) => {
    const start = heading.index + heading[0].length;
    const end = headings[index + 1]?.index ?? body.length;
    return { title: heading[1].trim(), text: body.slice(start, end).trim() };
  });
}

function matchingSection(parts, pattern) {
  return parts.find(({ title }) => pattern.test(title))?.text ?? "";
}

function brief(result, messageId) {
  if (result.errors.length > 0) {
    for (const error of result.errors) console.error(`error: ${error}`);
    console.error("mailbox brief requires a valid mailbox; run `scripts/mailbox check`");
    process.exitCode = 1;
    return;
  }
  const message = result.messages.find(({ header }) => header["message-id"] === messageId);
  if (!message) {
    console.error(`error: mailbox message not found: ${messageId}`);
    process.exitCode = 1;
    return;
  }
  const { header, body } = message;
  const identity = [
    `base=${header.base}`,
    `head=${header.head}`,
    `branch=${header.branch}`,
    `worktree=${header.worktree}`,
  ].filter((entry) => !entry.endsWith("=undefined"));
  console.log(`${header["message-id"]} ${header.kind}/${header.state}: ${header.subject}`);
  if (identity.length > 0) console.log(identity.join(" "));
  const parts = sections(body);
  const outcome = matchingSection(parts, /outcome|result|decision|scope|blocker/i) || body;
  const validation = matchingSection(parts, /validation|checks|evidence/i);
  const next = matchingSection(parts, /remaining|next|stop|follow-up/i);
  console.log(`outcome: ${compactText(outcome)}`);
  if (validation) console.log(`validation: ${compactText(validation)}`);
  if (next) console.log(`next: ${compactText(next)}`);
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
    console.error("mailbox list requires a valid mailbox; run `scripts/mailbox check`");
    process.exitCode = 1;
    return;
  }
  const selectedStates = options.states.size > 0 ? options.states : defaultListStates;
  const addressMatches = (thread) => {
    if (!options.address) return true;
    if (thread.owner === options.address || thread.to === options.address) return true;
    const project = options.address.split("/", 1)[0];
    return thread.to === `${project}/*`;
  };
  const threads = result.threads.filter((thread) =>
    (options.all || selectedStates.has(thread.state)) && addressMatches(thread));
  if (options.json) {
    console.log(JSON.stringify({
      protocol: mailboxProtocol,
      mailbox: result.mailboxPath,
      ignoredFiles: result.ignoredFiles,
      filter: {
        states: options.all ? "all" : [...selectedStates],
        address: options.address,
      },
      threads,
    }, null, 2));
    return;
  }
  if (options.verbose) printWarnings(result);
  if (threads.length === 0) {
    console.log(options.all ? "no mailbox threads" : "no actionable mailbox threads");
    return;
  }
  for (const thread of threads) {
    const owner = thread.owner ? ` owner=${thread.owner}` : "";
    const disposition = thread.disposition ? ` disposition=${thread.disposition}` : "";
    console.log(
      `${thread.state.padEnd(11)} ${thread.threadId} ${thread.from} -> ` +
      `${thread.to}${owner}${disposition}: ${thread.subject}`,
    );
    if (!options.verbose) continue;
    const count = `${thread.messageCount} message${thread.messageCount === 1 ? "" : "s"}`;
    console.log(`  ${count}; tail ${thread.tail}`);
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

const argv = process.argv.slice(2);
let options;
if (argv.length === 1 && new Set(["help", "-h", "--help"]).has(argv[0])) {
  usage(console.log);
} else {
  try {
    options = parseArgs(argv);
  } catch (error) {
    console.error(`error: ${error.message}`);
    usage();
    process.exit(2);
  }
}

if (options) {
  try {
    const mailboxPath = resolveMailbox({ mailbox: options.mailbox });
    const createsMailbox = options.command === "deliver" ||
      (options.command === "route" && options.routeAction === "bind");
    if (!createsMailbox && options.mailbox && !existsSync(mailboxPath)) {
      throw new Error(`mailbox does not exist: ${mailboxPath}`);
    }
    if (options.command === "deliver") {
      const delivered = deliverMessage(mailboxPath, options.draft);
      console.log(`delivered ${delivered.messageId} -> ${delivered.destination}`);
      if (options.noNotify) {
        console.log(`Codex notification skipped for ${delivered.messageId}`);
      } else {
        let session = options.notifySession;
        let label = session;
        if (!session) {
          try {
            const route = resolveCodexRoute(mailboxPath, delivered.to);
            session = route.sessionId;
            label = `${route.sessionName} (${route.sessionId})`;
          } catch (error) {
            console.warn(
              `warning: mailbox message ${delivered.messageId} is durably delivered, but ` +
              `Codex route resolution failed: ${error.message}`,
            );
          }
        }
        if (session) {
          const notification = notifyCodexSession(session, delivered);
          if (notification.ok) console.log(`notified Codex session ${label}`);
          else console.warn(
            `warning: mailbox message ${delivered.messageId} is durably delivered, but ` +
            `Codex notification failed: ${notification.detail}`,
          );
        }
      }
    } else if (options.command === "route") {
      if (options.routeAction === "bind") {
        const route = bindCodexRoute(mailboxPath, options.routeAddress,
          options.routeSession);
        console.log(`bound ${route.address} -> ${route.sessionName} (${route.sessionId})`);
      } else if (options.routeAction === "unbind") {
        const removed = unbindCodexRoute(mailboxPath, options.routeAddress);
        console.log(removed ? `unbound ${options.routeAddress}` :
          `no route bound for ${options.routeAddress}`);
      } else {
        const registry = readCodexRoutes(mailboxPath);
        if (options.json) console.log(JSON.stringify(registry, null, 2));
        else if (registry.routes.length === 0) console.log("no Codex mailbox routes");
        else for (const route of registry.routes) {
          console.log(`${route.address} -> ${route.sessionName} (${route.sessionId})`);
        }
      }
    } else {
      const result = inspectMailbox(mailboxPath);
      if (options.command === "check") check(result);
      else if (options.command === "brief") brief(result, options.messageId);
      else list(result, options);
    }
  } catch (error) {
    console.error(`error: ${error.message}`);
    process.exitCode = 1;
  }
}
