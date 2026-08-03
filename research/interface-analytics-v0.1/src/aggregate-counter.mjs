export const EVENT_KINDS = Object.freeze([
  "page_view",
  "reader_open",
  "language_switch",
  "support_open",
]);

export const ROUTES = Object.freeze({
  "/e/page-view": "page_view",
  "/e/reader-open": "reader_open",
  "/e/language-switch": "language_switch",
  "/e/support-open": "support_open",
});

export const RETENTION_DAYS = 35;
export const MAX_COUNTER = 2_147_483_647;
export const SCHEMA = "p1.aggregate.v1";

const DAY_PATTERN = /^\d{4}-\d{2}-\d{2}$/;
const owns = (object, key) => Object.prototype.hasOwnProperty.call(object, key);

function assertPositiveInteger(value, label) {
  if (!Number.isSafeInteger(value) || value < 1) {
    throw new TypeError(`${label} must be a positive safe integer`);
  }
}

function assertDay(day) {
  if (typeof day !== "string" || !DAY_PATTERN.test(day)) {
    throw new TypeError("day must be a YYYY-MM-DD UTC bucket");
  }
}

function assertKind(kind) {
  if (!EVENT_KINDS.includes(kind)) {
    throw new TypeError("event kind is not allowlisted");
  }
}

function optionsWithDefaults(options = {}) {
  const retentionDays = options.retentionDays ?? RETENTION_DAYS;
  const maxCount = options.maxCount ?? MAX_COUNTER;
  assertPositiveInteger(retentionDays, "retentionDays");
  assertPositiveInteger(maxCount, "maxCount");
  return { retentionDays, maxCount };
}

export function emptyState() {
  return Object.freeze({ schema: SCHEMA, days: Object.freeze({}) });
}

export function serverDay(serverNow) {
  const instant = serverNow instanceof Date ? new Date(serverNow.getTime()) : new Date(serverNow);
  if (Number.isNaN(instant.getTime())) {
    throw new TypeError("serverNow must be a valid server-owned instant");
  }
  return instant.toISOString().slice(0, 10);
}

export function decodeRoute(route) {
  return typeof route === "string" && owns(ROUTES, route) ? ROUTES[route] : null;
}

export function sanitizeIngress(envelope, serverNow) {
  if (!envelope || typeof envelope !== "object") return null;
  if (envelope.method !== "POST") return null;
  if (envelope.bodyBytes !== 0) return null;

  const kind = decodeRoute(envelope.route);
  if (kind === null) return null;

  return Object.freeze({ day: serverDay(serverNow), kind });
}

function copyAndValidateState(state, maxCount) {
  if (!state || state.schema !== SCHEMA || !state.days || typeof state.days !== "object" || Array.isArray(state.days)) {
    throw new TypeError("invalid aggregate state");
  }

  const days = Object.create(null);
  for (const [day, sourceCounts] of Object.entries(state.days)) {
    assertDay(day);
    if (!sourceCounts || typeof sourceCounts !== "object" || Array.isArray(sourceCounts)) {
      throw new TypeError("invalid day counter");
    }

    const counts = Object.create(null);
    for (const [kind, count] of Object.entries(sourceCounts)) {
      assertKind(kind);
      if (!Number.isSafeInteger(count) || count < 0 || count > maxCount) {
        throw new TypeError("counter is outside the configured bound");
      }
      counts[kind] = count;
    }
    days[day] = counts;
  }
  return days;
}

function freezeState(days) {
  const frozenDays = {};
  for (const day of Object.keys(days).sort()) {
    frozenDays[day] = Object.freeze({ ...days[day] });
  }
  return Object.freeze({ schema: SCHEMA, days: Object.freeze(frozenDays) });
}

export function applySafeEvent(state, event, options = {}) {
  const { retentionDays, maxCount } = optionsWithDefaults(options);
  if (!event || typeof event !== "object") throw new TypeError("safe event is required");
  assertDay(event.day);
  assertKind(event.kind);

  const days = copyAndValidateState(state, maxCount);
  const counts = days[event.day] ?? Object.create(null);
  const current = counts[event.kind] ?? 0;
  counts[event.kind] = Math.min(maxCount, current + 1);
  days[event.day] = counts;

  const retained = Object.keys(days).sort().slice(-retentionDays);
  const boundedDays = Object.create(null);
  for (const day of retained) boundedDays[day] = days[day];
  return freezeState(boundedDays);
}

export function ingest(state, envelope, serverNow, options = {}) {
  const event = sanitizeIngress(envelope, serverNow);
  if (event === null) return Object.freeze({ accepted: false, state });
  return Object.freeze({ accepted: true, state: applySafeEvent(state, event, options) });
}

export function snapshot(state, options = {}) {
  const { maxCount } = optionsWithDefaults(options);
  return freezeState(copyAndValidateState(state, maxCount));
}
