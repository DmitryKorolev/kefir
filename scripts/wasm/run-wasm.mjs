// Run the wasm32-wasip1 build of kefir under Node's WASI.
//
//   node run-wasm.mjs kefir.wasm <export.ndjson> [kefir arguments...]
//
// The module runs in a worker thread whose engine stack is ENGINE_STACK_MB, sized
// for the kernel's deepest permitted recursion. The report is the
// module's own stdout. Exit codes 0-3 pass through; a trap, an engine-stack
// overflow or any host failure exits 3 and is never a verdict.
import { readFile } from "node:fs/promises";
import { realpathSync } from "node:fs";
import path from "node:path";
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { WASI } from "node:wasi";

const ENGINE_STACK_MB = 2048;

if (isMainThread) {
  // Node exits 1 on an uncaught exception, which would read as "reject". Any
  // failure of the host itself is an internal failure: exit 3.
  process.on("uncaughtException", () => process.exit(3));
  process.on("unhandledRejection", () => process.exit(3));
  try {
    main();
  } catch {
    process.exit(3);
  }
}

function main() {
  // Until the worker reports the module's own exit code, the result is 3.
  process.exitCode = 3;
  const [wasmPath, input, ...args] = process.argv.slice(2);
  if (!wasmPath || !input) {
    process.stderr.write("usage: node run-wasm.mjs kefir.wasm <export.ndjson> [args...]\n");
    process.exit(3);
  }
  // WASI cannot follow a symlink out of its preopened directory: resolve it first.
  let real;
  try {
    real = realpathSync(input);
  } catch {
    // Let the module report the unreadable input itself.
    real = path.resolve(input);
  }
  const worker = new Worker(new URL(import.meta.url), {
    workerData: { wasmPath, real, args },
    resourceLimits: { stackSizeMb: ENGINE_STACK_MB },
    stdout: false,
    stderr: false,
  });
  let code = 3;
  worker.on("message", (message) => {
    if (Number.isInteger(message) && message >= 0 && message <= 3) code = message;
  });
  worker.on("error", (error) => {
    code = 3;
    try {
      process.stderr.write(`run-wasm: ${error && error.message ? error.message : error}\n`);
    } catch {
      // Reporting the failure must not change the exit code.
    }
  });
  worker.on("exit", () => {
    process.exitCode = code;
  });
}

if (!isMainThread) {
  const { wasmPath, real, args } = workerData;
  const wasi = new WASI({
    version: "preview1",
    args: ["kefir", ...args],
    env: { IN: path.join("/in", path.basename(real)) },
    preopens: { "/in": path.dirname(real) },
    returnOnExit: true,
  });
  const module = await WebAssembly.compile(await readFile(wasmPath));
  const instance = await WebAssembly.instantiate(module, wasi.getImportObject());
  // A trap or stack overflow throws here and reaches the parent's "error" handler.
  parentPort.postMessage(wasi.start(instance));
}
