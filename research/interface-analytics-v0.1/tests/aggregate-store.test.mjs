import test from "node:test";
import assert from "node:assert/strict";
import { emptyState } from "../src/aggregate-counter.mjs";
import {
  MemoryAggregateStore,
  mountAnalyticsCapability,
} from "../src/aggregate-store.mjs";

const ORIGIN = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site";
const NOW = "2026-07-31T12:00:00Z";
const request = (index = 0) => ({
  method: "POST",
  url: `${ORIGIN}/e/page-view`,
  body: null,
  headers: { "user-agent": `FORBIDDEN-UA-${index}` },
  ip: `198.51.100.${index % 255}`,
  visitorId: `FORBIDDEN-ID-${index}`,
});
const mount = (store, overrides = {}) => mountAnalyticsCapability({
  store,
  expectedOrigin: ORIGIN,
  ...overrides,
});

test("missing storage capability keeps analytics unmounted", () => {
  assert.equal(mountAnalyticsCapability(), null);
  assert.equal(mountAnalyticsCapability({ store: null }), null);
});

test("serializes concurrent increments without lost updates", async () => {
  const store = new MemoryAggregateStore();
  const capability = mount(store, { dailyBudget: 1_000 });
  const responses = await Promise.all(Array.from({ length: 128 }, (_, index) => capability.handle(request(index), NOW)));
  assert.equal(responses.every((response) => response.status === 204), true);
  const state = await store.snapshotForTest();
  assert.equal(state.days["2026-07-31"].page_view, 128);
});

test("global budget remains exact under concurrency", async () => {
  const store = new MemoryAggregateStore();
  const capability = mount(store, { dailyBudget: 7 });
  const responses = await Promise.all(Array.from({ length: 64 }, (_, index) => capability.handle(request(index), NOW)));
  assert.equal(responses.filter((response) => response.status === 204).length, 7);
  assert.equal(responses.filter((response) => response.status === 429).length, 57);
  const state = await store.snapshotForTest();
  assert.equal(state.days["2026-07-31"].page_view, 7);
});

test("failed transition rolls back and does not poison the queue", async () => {
  const store = new MemoryAggregateStore();
  await assert.rejects(store.transact(() => {
    throw new Error("synthetic failure");
  }));
  assert.deepEqual(await store.snapshotForTest(), emptyState());
  const capability = mount(store);
  assert.equal((await capability.handle(request(), NOW)).status, 204);
  assert.equal((await store.snapshotForTest()).days["2026-07-31"].page_view, 1);
});

test("storage failure becomes an empty 503 response", async () => {
  const capability = mount({
    async transact() {
      throw new Error("provider unavailable");
    },
  });
  assert.deepEqual(await capability.handle(request(), NOW), { status: 503, body: null, headers: {} });
});

test("wire response never exposes state, reason, identity or count", async () => {
  const store = new MemoryAggregateStore();
  const response = await mount(store).handle(request(), NOW);
  assert.deepEqual(response, { status: 204, body: null, headers: {} });
  const serialized = JSON.stringify(response);
  for (const marker of ["state", "reason", "count", "FORBIDDEN", "visitor", "198.51.100"] ) {
    assert.equal(serialized.includes(marker), false);
  }
});

test("stored representation contains only aggregate schema", async () => {
  const store = new MemoryAggregateStore();
  await mount(store).handle(request(42), NOW);
  const serialized = JSON.stringify(await store.snapshotForTest());
  assert.equal(serialized, '{"schema":"p1.aggregate.v1","days":{"2026-07-31":{"page_view":1}}}');
});

test("invalid storage capability fails before mounting", () => {
  assert.throws(() => mountAnalyticsCapability({ store: {}, expectedOrigin: ORIGIN }));
});
