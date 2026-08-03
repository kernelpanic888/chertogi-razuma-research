import test from "node:test";
import assert from "node:assert/strict";
import * as counter from "../src/aggregate-counter.mjs";

const validEnvelope = (overrides = {}) => ({
  method: "POST",
  route: "/e/page-view",
  bodyBytes: 0,
  ...overrides,
});

test("accepts only an exact bodyless POST route", () => {
  const now = "2026-07-31T23:59:59Z";
  assert.deepEqual(counter.sanitizeIngress(validEnvelope(), now), {
    day: "2026-07-31",
    kind: "page_view",
  });
  assert.equal(counter.sanitizeIngress(validEnvelope({ method: "GET" }), now), null);
  assert.equal(counter.sanitizeIngress(validEnvelope({ bodyBytes: 1 }), now), null);
  assert.equal(counter.sanitizeIngress(validEnvelope({ route: "/e/page-view?x=1" }), now), null);
  assert.equal(counter.sanitizeIngress(validEnvelope({ route: "/e/unknown" }), now), null);
});

test("server assigns the UTC day", () => {
  const event = counter.sanitizeIngress(
    validEnvelope({ clientDay: "1900-01-01" }),
    "2026-08-01T00:00:00+02:00",
  );
  assert.equal(event.day, "2026-07-31");
});

test("forbidden metadata cannot influence the safe event", () => {
  const publicPart = validEnvelope({ route: "/e/reader-open" });
  const a = { ...publicPart, ip: "198.51.100.1", userAgent: "CANARY-UA-A", referrer: "CANARY-REF-A", cookie: "CANARY-COOKIE-A", visitorId: "CANARY-ID-A" };
  const b = { ...publicPart, ip: "203.0.113.250", userAgent: "CANARY-UA-B", referrer: "CANARY-REF-B", cookie: "CANARY-COOKIE-B", visitorId: "CANARY-ID-B" };
  assert.deepEqual(counter.sanitizeIngress(a, "2026-07-31T10:00:00Z"), counter.sanitizeIngress(b, "2026-07-31T10:00:00Z"));

  const resultA = counter.ingest(counter.emptyState(), a, "2026-07-31T10:00:00Z");
  const resultB = counter.ingest(counter.emptyState(), b, "2026-07-31T10:00:00Z");
  assert.deepEqual(resultA, resultB);
  const output = JSON.stringify(resultA);
  for (const forbidden of ["198.51.100.1", "CANARY-UA", "CANARY-REF", "CANARY-COOKIE", "CANARY-ID"]) {
    assert.equal(output.includes(forbidden), false);
  }
});

test("counts events without mutating the input state", () => {
  const initial = counter.emptyState();
  const before = JSON.stringify(initial);
  const first = counter.ingest(initial, validEnvelope(), "2026-07-31T10:00:00Z");
  const second = counter.ingest(first.state, validEnvelope(), "2026-07-31T11:00:00Z");
  assert.equal(JSON.stringify(initial), before);
  assert.equal(second.state.days["2026-07-31"].page_view, 2);
});

test("retains only the newest configured UTC days", () => {
  let state = counter.emptyState();
  for (let day = 1; day <= 40; day += 1) {
    const now = new Date(Date.UTC(2026, 0, day));
    state = counter.ingest(state, validEnvelope(), now).state;
  }
  const days = Object.keys(state.days);
  assert.equal(days.length, counter.RETENTION_DAYS);
  assert.equal(days[0], "2026-01-06");
  assert.equal(days.at(-1), "2026-02-09");
});

test("counter saturates instead of overflowing", () => {
  const options = { maxCount: 2 };
  let state = counter.emptyState();
  for (let index = 0; index < 5; index += 1) {
    state = counter.ingest(state, validEnvelope(), "2026-07-31T10:00:00Z", options).state;
  }
  assert.equal(state.days["2026-07-31"].page_view, 2);
});

test("rejects forged state keys and out-of-range counters", () => {
  assert.throws(() => counter.snapshot({ schema: counter.SCHEMA, days: { "2026-07-31": { visitor_id: 1 } } }));
  assert.throws(() => counter.snapshot({ schema: counter.SCHEMA, days: { "2026-07-31": { page_view: -1 } } }));
});

test("public module exposes no unique-visitor operation", () => {
  assert.equal(Object.keys(counter).some((name) => /unique|visitor|fingerprint/i.test(name)), false);
});
