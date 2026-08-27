/*
 * PM-01 browser wrapper for the Lean definitions in PoetryOfMathematics.lean.
 *
 * This is an operational projection for the public reader. It is not generated
 * from Lean, is not a proof checker, and does not establish implementation
 * equivalence with the kernel-checked source. The reader exposes that boundary.
 */
(function exposeHypothesisOrbitWrapper(globalScope) {
  "use strict";

  const EpistemicStatus = Object.freeze({
    hypothesis: "hypothesis",
    verifiedFact: "verifiedFact"
  });

  function hypothesisState({ hypothesis, radius, angle, status = EpistemicStatus.hypothesis }) {
    if (typeof hypothesis !== "string" || hypothesis.length === 0) {
      throw new TypeError("hypothesis must be a non-empty string");
    }
    if (!Number.isFinite(radius) || radius < 0) {
      throw new RangeError("radius must be a finite nonnegative number");
    }
    if (!Number.isFinite(angle)) {
      throw new TypeError("angle must be finite");
    }
    if (!Object.values(EpistemicStatus).includes(status)) {
      throw new TypeError("unknown epistemic status");
    }
    return Object.freeze({ hypothesis, radius, angle, status });
  }

  function dRadius(before, after) {
    return after.radius - before.radius;
  }

  function dTheta(before, after) {
    return after.angle - before.angle;
  }

  function rotateBy(state, deltaTheta) {
    if (!Number.isFinite(deltaTheta)) throw new TypeError("deltaTheta must be finite");
    return hypothesisState({ ...state, angle: state.angle + deltaTheta });
  }

  function radialCandidate(state, deltaRadius) {
    if (!Number.isFinite(deltaRadius)) throw new TypeError("deltaRadius must be finite");
    return hypothesisState({ ...state, radius: Math.max(0, state.radius + deltaRadius) });
  }

  function promotionCandidate(state) {
    return hypothesisState({ ...state, status: EpistemicStatus.verifiedFact });
  }

  function admissibility(independentlyVerified, before, after) {
    const sameHypothesis = after.hypothesis === before.hypothesis;
    const inward = dRadius(before, after) < 0;
    const promotion = before.status === EpistemicStatus.hypothesis
      && after.status === EpistemicStatus.verifiedFact;
    const inwardGate = !inward || independentlyVerified === true;
    const promotionGate = !promotion || independentlyVerified === true;
    return Object.freeze({
      sameHypothesis,
      inward,
      promotion,
      independentlyVerified: independentlyVerified === true,
      allowed: sameHypothesis && inwardGate && promotionGate
    });
  }

  function tryRadialMove(state, deltaRadius, independentlyVerified) {
    const candidate = radialCandidate(state, deltaRadius);
    const gate = admissibility(independentlyVerified, state, candidate);
    return Object.freeze({ ok: gate.allowed, before: state, candidate, after: gate.allowed ? candidate : state, gate });
  }

  function tryPromotion(state, independentlyVerified) {
    const candidate = promotionCandidate(state);
    const gate = admissibility(independentlyVerified, state, candidate);
    return Object.freeze({ ok: gate.allowed, before: state, candidate, after: gate.allowed ? candidate : state, gate });
  }

  const api = Object.freeze({
    EpistemicStatus,
    hypothesisState,
    dRadius,
    dTheta,
    rotateBy,
    radialCandidate,
    promotionCandidate,
    admissibility,
    tryRadialMove,
    tryPromotion
  });

  globalScope.HypothesisOrbitWrapper = api;
  if (typeof module !== "undefined" && module.exports) module.exports = api;
})(typeof globalThis !== "undefined" ? globalThis : window);
