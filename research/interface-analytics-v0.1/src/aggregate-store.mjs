import { emptyState, snapshot } from "./aggregate-counter.mjs";
import { admitAggregateRequest } from "./network-adapter.mjs";

function wireResponse(status) {
  return Object.freeze({
    status,
    body: null,
    headers: Object.freeze({}),
  });
}

export class MemoryAggregateStore {
  #state;
  #tail = Promise.resolve();

  constructor(initialState = emptyState()) {
    this.#state = snapshot(initialState);
  }

  transact(transition) {
    if (typeof transition !== "function") {
      return Promise.reject(new TypeError("transition must be a function"));
    }

    const operation = this.#tail.then(async () => {
      const outcome = await transition(this.#state);
      if (!outcome || typeof outcome !== "object" || !("state" in outcome) || !("value" in outcome)) {
        throw new TypeError("transition must return state and value");
      }
      const nextState = snapshot(outcome.state);
      this.#state = nextState;
      return outcome.value;
    });

    this.#tail = operation.then(
      () => undefined,
      () => undefined,
    );
    return operation;
  }

  async snapshotForTest() {
    await this.#tail;
    return snapshot(this.#state);
  }
}

export function mountAnalyticsCapability(configuration = {}) {
  const store = configuration.store;
  if (store === null || store === undefined) return null;
  if (typeof store.transact !== "function") {
    throw new TypeError("store must provide an atomic transact operation");
  }

  const adapterOptions = Object.freeze({
    expectedOrigin: configuration.expectedOrigin,
    dailyBudget: configuration.dailyBudget,
  });

  return Object.freeze({
    async handle(request, serverNow) {
      try {
        return await store.transact((state) => {
          const decision = admitAggregateRequest(state, request, serverNow, adapterOptions);
          return {
            state: decision.state,
            value: wireResponse(decision.status),
          };
        });
      } catch {
        return wireResponse(503);
      }
    },
  });
}
