import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const CASES = 768;
const RETENTION_DAYS = 35;
const routes = [
  ["/e/page-view", "page_view"],
  ["/e/reader-open", "reader_open"],
  ["/e/language-switch", "language_switch"],
  ["/e/support-open", "support_open"],
];

let seed = 0x51f17a3d;
const next = () => {
  seed ^= seed << 13;
  seed ^= seed >>> 17;
  seed ^= seed << 5;
  return seed >>> 0;
};

const commands = [];
const oracle = {};
let accepted = 0;

for (let index = 0; index < CASES; index += 1) {
  const [baseRoute, kind] = routes[next() % routes.length];
  const dayOffset = next() % 50;
  const serverNow = new Date(Date.UTC(2026, 0, 1 + dayOffset, next() % 24)).toISOString();
  const envelope = {
    method: "POST",
    route: baseRoute,
    bodyBytes: 0,
    ip: `198.51.100.${index % 255}`,
    userAgent: `BLIND-UA-${index}-${next()}`,
    referrer: `https://forbidden.example/private/${index}`,
    cookie: `BLIND-COOKIE-${index}-${next()}`,
    visitorId: `BLIND-VISITOR-${index}-${next()}`,
  };

  if (index % 17 === 0) envelope.method = "GET";
  else if (index % 19 === 0) envelope.bodyBytes = 1;
  else if (index % 23 === 0) envelope.route = `${baseRoute}?visitor=${index}`;
  else if (index % 29 === 0) envelope.route = "/e/not-allowlisted";

  commands.push(JSON.stringify({ serverNow, envelope }));

  if (envelope.method === "POST" && envelope.bodyBytes === 0 && envelope.route === baseRoute) {
    const day = serverNow.slice(0, 10);
    oracle[day] ??= {};
    oracle[day][kind] = (oracle[day][kind] ?? 0) + 1;
    accepted += 1;
  }
}

const retainedDays = Object.keys(oracle).sort().slice(-RETENTION_DAYS);
const expectedDays = {};
for (const day of retainedDays) expectedDays[day] = oracle[day];

const cli = fileURLToPath(new URL("../src/counter-cli.mjs", import.meta.url));
const candidate = spawnSync(process.execPath, [cli], {
  input: `${commands.join("\n")}\n`,
  encoding: "utf8",
  maxBuffer: 4 * 1024 * 1024,
});

assert.equal(candidate.status, 0, candidate.stderr);
assert.equal(candidate.stderr, "");
const rawOutput = candidate.stdout.trim();
const observed = JSON.parse(rawOutput);
assert.deepEqual(observed, { schema: "p1.aggregate.v1", days: expectedDays });
assert.equal(Object.keys(observed.days).length, RETENTION_DAYS);

const forbiddenMarkers = [
  "198.51.100.",
  "BLIND-UA-",
  "forbidden.example",
  "BLIND-COOKIE-",
  "BLIND-VISITOR-",
  "visitorId",
  "userAgent",
  "referrer",
  "cookie",
  "ip",
];
for (const marker of forbiddenMarkers) assert.equal(rawOutput.includes(marker), false, marker);

process.stdout.write([
  "test_id=P1-AC-BLIND-01",
  `seed=0x51f17a3d`,
  `cases=${CASES}`,
  `accepted=${accepted}`,
  `retained_days=${Object.keys(observed.days).length}`,
  `forbidden_markers_found=0/${forbiddenMarkers.length}`,
  "candidate_stderr=empty",
  "verdict=PASS",
  "boundary=ENGINEERING_BLACK_BOX_NOT_EXTERNAL_EMPIRICAL_VALIDATION",
].join("\n") + "\n");
