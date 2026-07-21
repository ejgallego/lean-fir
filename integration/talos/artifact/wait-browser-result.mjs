const debugUrl = process.argv[2];
const pageUrl = process.argv[3];
const timeoutSeconds = Number(process.argv[4] ?? "15");
if (!debugUrl || !pageUrl || !Number.isFinite(timeoutSeconds) || timeoutSeconds <= 0) {
  throw new Error(
    "usage: node wait-browser-result.mjs DEBUG_URL PAGE_URL [TIMEOUT_SECONDS]",
  );
}

const deadline = Date.now() + timeoutSeconds * 1000;
const pause = () => new Promise((resolve) => setTimeout(resolve, 50));

async function findPageTarget() {
  while (Date.now() < deadline) {
    try {
      const response = await fetch(`${debugUrl}/json/list`);
      if (response.ok) {
        const targets = await response.json();
        const target = targets.find((candidate) =>
          candidate.type === "page" && candidate.url === pageUrl);
        if (target) {
          return target;
        }
      }
    } catch {
      // Chrome may not have opened its debugging socket yet.
    }
    await pause();
  }
  throw new Error(`browser page did not appear at ${pageUrl}`);
}

const target = await findPageTarget();
const socket = new WebSocket(target.webSocketDebuggerUrl);
await new Promise((resolve, reject) => {
  socket.addEventListener("open", resolve, { once: true });
  socket.addEventListener("error", reject, { once: true });
});

let nextId = 1;
const pending = new Map();
socket.addEventListener("message", (event) => {
  const message = JSON.parse(event.data);
  const continuation = pending.get(message.id);
  if (continuation) {
    pending.delete(message.id);
    continuation(message);
  }
});

function evaluate(expression) {
  const id = nextId++;
  const result = new Promise((resolve) => pending.set(id, resolve));
  socket.send(JSON.stringify({
    id,
    method: "Runtime.evaluate",
    params: { expression, returnByValue: true },
  }));
  return result;
}

try {
  while (Date.now() < deadline) {
    const response = await evaluate("document.documentElement.dataset.result");
    const state = response.result?.result?.value;
    if (state === "pass") {
      const output = await evaluate("document.querySelector('#result').textContent");
      console.log(output.result?.result?.value);
      process.exitCode = 0;
      break;
    }
    if (state === "fail") {
      const output = await evaluate("document.querySelector('#result').textContent");
      throw new Error(output.result?.result?.value ?? "browser check failed");
    }
    await pause();
  }
  if (process.exitCode === undefined) {
    throw new Error(`timed out after ${timeoutSeconds}s waiting for browser result`);
  }
} finally {
  socket.close();
}
