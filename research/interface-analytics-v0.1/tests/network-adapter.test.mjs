import test from "node:test";
import assert from "node:assert/strict";
import { emptyState } from "../src/aggregate-counter.mjs";
import {
  admitAggregateRequest,
  projectNetworkRequest,
} from "../src/network-adapter.mjs";

const ORIGIN = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site";
const NOW = "2026-07-31T12:00:00Z";
const request = (overrides = {}) => ({
  method: "POST",
  url: `${ORIGIN}/e/page-view`,
  body: null,
  ...overrides,
});
const options = (overrides = {}) => ({ expectedOrigin: ORIGIN, ...overrides });

test("projects the minimum bodyless HTTPS request", () => {
  assert.deepEqual(projectNetworkRequest(request(), ORIGIN), {
    accepted: true,
    status: 204,
    envelope: { method: "POST", route: "/e/page-view", bodyBytes: 0 },
  });
});

test("rejects methods, bodies, URL details, origins and unknown routes", () => {
  assert.equal(projectNetworkRequest(request({ method: "GET" }), ORIGIN).status, 405);
  assert.equal(projectNetworkRequest(request({ body: "" }), ORIGIN).status, 413);
  assert.equal(projectNetworkRequest(request({ url: `${ORIGIN}/e/page-view?x=1` }), ORIGIN).status, 400);
  assert.equal(projectNetworkRequest(request({ url: "https://example.org/e/page-view" }), ORIGIN).status, 403);
  assert.equal(projectNetworkRequest(request({ url: `${ORIGIN}/e/unknown` }), ORIGIN).status, 404);
});

test("capability trap proves forbidden request properties are not read", () => {
  const allowed = request();
  const forbidden = new Set(["headers", "cf", "ip", "userAgent", "referrer", "cookie", "visitorId"]);
  const trapped = new Proxy(allowed, {
    get(target, property, receiver) {
      if (forbidden.has(property)) throw new Error(`forbidden capability read: ${String(property)}`);
      return Reflect.get(target, property, receiver);
    },
  });
  assert.equal(admitAggregateRequest(emptyState(), trapped, NOW, options()).status, 204);
});

test("hidden actor metadata cannot change an isolated decision", () => {
  const human = request({ headers: { "user-agent": "HUMAN-CANARY" }, ip: "198.51.100.8", visitorId: "HUMAN-ID" });
  const bot = request({ headers: { "user-agent": "BOT-CANARY" }, ip: "203.0.113.9", visitorId: "BOT-ID" });
  const left = admitAggregateRequest(emptyState(), human, NOW, options());
  const right = admitAggregateRequest(emptyState(), bot, NOW, options());
  assert.deepEqual(left, right);
  const output = JSON.stringify(left);
  for (const marker of ["HUMAN", "BOT", "198.51.100.8", "203.0.113.9", "visitorId", "headers"]) {
    assert.equal(output.includes(marker), false);
  }
});

test("global daily budget bounds accepted work without identity", () => {
  let state = emptyState();
  for (let index = 0; index < 3; index += 1) {
    const result = admitAggregateRequest(state, request(), NOW, options({ dailyBudget: 3 }));
    assert.equal(result.status, 204);
    state = result.state;
  }
  const blocked = admitAggregateRequest(state, request(), NOW, options({ dailyBudget: 3 }));
  assert.equal(blocked.status, 429);
  assert.equal(blocked.accepted, false);
  assert.strictEqual(blocked.state, state);
});

test("rejected network input leaves aggregate state untouched", () => {
  const state = emptyState();
  const result = admitAggregateRequest(state, request({ body: "forbidden" }), NOW, options());
  assert.equal(result.accepted, false);
  assert.strictEqual(result.state, state);
});

test("accepted result exposes no body, headers, cookie or count", () => {
  const result = admitAggregateRequest(emptyState(), request(), NOW, options());
  assert.deepEqual(Object.keys(result).sort(), ["accepted", "reason", "state", "status"]);
  for (const field of ["body", "headers", "cookie", "count", "visitorId"]) {
    assert.equal(Object.hasOwn(result, field), false);
  }
});

test("invalid adapter configuration fails closed", () => {
  assert.throws(() => admitAggregateRequest(emptyState(), request(), NOW, options({ dailyBudget: 0 })));
  assert.throws(() => projectNetworkRequest(request(), "http://example.org"));
});
