import { createInterface } from "node:readline";
import { emptyState, ingest, snapshot } from "./aggregate-counter.mjs";

let state = emptyState();
const input = createInterface({ input: process.stdin, crlfDelay: Infinity });

for await (const line of input) {
  if (line.trim() === "") continue;
  const command = JSON.parse(line);
  const result = ingest(state, command.envelope, command.serverNow);
  state = result.state;
}

process.stdout.write(`${JSON.stringify(snapshot(state))}\n`);
