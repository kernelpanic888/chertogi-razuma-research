import {
  decodeRoute,
  ingest,
  serverDay,
  snapshot,
} from "./aggregate-counter.mjs";

export const DEFAULT_DAILY_BUDGET = 100_000;

function immutableResult(status, accepted, state, reason) {
  return Object.freeze({ status, accepted, state, reason });
}

function normalizedOrigin(expectedOrigin) {
  const url = new URL(expectedOrigin);
  if (url.protocol !== "https:" || url.username !== "" || url.password !== "" || url.search !== "" || url.hash !== "" || url.pathname !== "/") {
    throw new TypeError("expectedOrigin must be a bare HTTPS origin");
  }
  return url.origin;
}

function reject(status, reason) {
  return Object.freeze({ accepted: false, status, reason });
}

export function projectNetworkRequest(request, expectedOrigin) {
  if (!request || typeof request !== "object") return reject(400, "malformed_request");

  const method = request.method;
  const rawUrl = request.url;
  const body = request.body;

  if (method !== "POST") return reject(405, "method_not_allowed");
  if (body !== null) return reject(413, "body_forbidden");
  if (typeof rawUrl !== "string") return reject(400, "malformed_url");

  let url;
  try {
    url = new URL(rawUrl);
  } catch {
    return reject(400, "malformed_url");
  }

  if (url.protocol !== "https:" || url.origin !== normalizedOrigin(expectedOrigin)) {
    return reject(403, "destination_forbidden");
  }
  if (url.username !== "" || url.password !== "" || url.search !== "" || url.hash !== "") {
    return reject(400, "url_detail_forbidden");
  }
  if (decodeRoute(url.pathname) === null) return reject(404, "route_not_found");

  return Object.freeze({
    accepted: true,
    status: 204,
    envelope: Object.freeze({ method, route: url.pathname, bodyBytes: 0 }),
  });
}

export function countForDay(state, day) {
  const safeState = snapshot(state);
  const counts = safeState.days[day] ?? {};
  return Object.values(counts).reduce((total, count) => total + count, 0);
}

export function admitAggregateRequest(state, request, serverNow, options = {}) {
  const expectedOrigin = options.expectedOrigin;
  const dailyBudget = options.dailyBudget ?? DEFAULT_DAILY_BUDGET;
  if (!Number.isSafeInteger(dailyBudget) || dailyBudget < 1) {
    throw new TypeError("dailyBudget must be a positive safe integer");
  }

  const projected = projectNetworkRequest(request, expectedOrigin);
  if (!projected.accepted) {
    return immutableResult(projected.status, false, state, projected.reason);
  }

  const day = serverDay(serverNow);
  if (countForDay(state, day) >= dailyBudget) {
    return immutableResult(429, false, state, "daily_budget_exhausted");
  }

  const transition = ingest(state, projected.envelope, serverNow);
  if (!transition.accepted) throw new Error("projection violated the aggregate contract");
  return immutableResult(204, true, transition.state, "accepted");
}
