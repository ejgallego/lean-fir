import { closeSync, existsSync, mkdirSync, openSync, renameSync, unlinkSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { archiveGuardName, inspectMailbox, terminalStates } from "./mailbox-lib.mjs";

// Conservative reference retention, including IDs mentioned in prose. Follow
// references transitively so a live thread's historical dependencies stay flat.
export function planArchive(mailboxPath) {
  const state = inspectMailbox(mailboxPath);
  if (state.errors.length) throw new Error(`mailbox must pass integrity checks before archive:\n${state.errors.join("\n")}`);
  const byId = new Map(state.messages.map((m) => [m.header["message-id"], m.header["thread-id"]]));
  const references = new Map(state.threads.map((t) => [t.threadId, new Set()]));
  for (const message of state.messages) {
    const text = `${Object.values(message.header).join(" ")}\n${message.body}`;
    for (const id of text.match(/\b[A-Z][A-Z0-9]*-[A-Z][A-Z0-9]*-[0-9]{8}-[0-9]{3}\b/g) ?? []) {
      if (byId.has(id)) references.get(message.header["thread-id"]).add(byId.get(id));
    }
  }
  const retained = new Set(state.threads.filter((t) => !terminalStates.has(t.state)).map((t) => t.threadId));
  for (const thread of retained) {
    for (const dependency of references.get(thread)) retained.add(dependency);
  }
  const threads = state.threads.filter((t) => terminalStates.has(t.state) && !retained.has(t.threadId));
  const selected = new Set(threads.map((t) => t.threadId));
  const files = state.messages.filter((m) => selected.has(m.header["thread-id"]) && !m.file.startsWith("archive/"))
    .map((m) => m.file);
  const pending = new Set(files.map((file) => byId.get(file.slice(0, -3))));
  return {
    threads: threads.filter((t) => pending.has(t.threadId)).map((t) => t.threadId),
    files,
    protectedTerminalThreads: state.threads.filter((t) => terminalStates.has(t.state) && retained.has(t.threadId)).length,
    reviewPendingThreads: state.threads.filter((t) => t.state === "completed").length,
  };
}

export function archiveMailbox(mailboxPath, { apply = false } = {}) {
  if (!apply) return planArchive(mailboxPath);
  if (!existsSync(mailboxPath)) throw new Error(`mailbox does not exist: ${mailboxPath}`);
  const temporary = resolve(mailboxPath, "tmp");
  mkdirSync(temporary, { recursive: true, mode: 0o700 });
  const lockPath = resolve(temporary, "delivery.lock");
  let lock;
  try {
    // Same lock as delivery. Never remove someone else's lock on failure.
    lock = openSync(lockPath, "wx", 0o600);
    const plan = planArchive(mailboxPath);
    if (!plan.files.length) return plan;
    // Old readers reject this non-event instead of silently ignoring archived
    // IDs during delivery. Current readers reserve it as migration metadata.
    const guard = resolve(mailboxPath, archiveGuardName);
    if (!existsSync(guard)) writeFileSync(guard,
      "# Archived mailbox history\n\nUse current main's scripts/mailbox; older tools do not validate archive/.\n",
      { flag: "wx", mode: 0o600 });
    const archive = resolve(mailboxPath, "archive");
    mkdirSync(archive, { recursive: true, mode: 0o700 });
    for (const file of plan.files) {
      if (existsSync(resolve(archive, file))) throw new Error(`archive destination already exists: ${file}`);
    }
    // Same-filesystem renames preserve exact bytes. Each message exists in
    // exactly one scanned directory, even if interrupted. Re-run to finish.
    for (const file of plan.files) renameSync(resolve(mailboxPath, file), resolve(archive, file));
    return plan;
  } finally {
    if (lock !== undefined) {
      closeSync(lock);
      unlinkSync(lockPath);
    }
  }
}
