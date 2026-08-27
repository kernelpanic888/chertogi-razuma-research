"use strict";

const assert = require("node:assert/strict");
const loaded = require("./hypothesis-orbit-wrapper.js");
const model = loaded.hypothesisState ? loaded : globalThis.HypothesisOrbitWrapper;

const H1 = model.hypothesisState({ hypothesis: "H1", radius: 3, angle: 0.4 });
const rotated = model.rotateBy(H1, 1.25);

assert.equal(model.dRadius(H1, rotated), 0);
assert.ok(Math.abs(model.dTheta(H1, rotated) - 1.25) < Number.EPSILON * 4);
assert.equal(rotated.status, H1.status);
assert.equal(rotated.hypothesis, H1.hypothesis);

const blockedInward = model.tryRadialMove(H1, -0.5, false);
assert.equal(blockedInward.ok, false);
assert.equal(blockedInward.after, H1);

const admittedInward = model.tryRadialMove(H1, -0.5, true);
assert.equal(admittedInward.ok, true);
assert.equal(admittedInward.after.radius, 2.5);

const blockedPromotion = model.tryPromotion(H1, false);
assert.equal(blockedPromotion.ok, false);
assert.equal(blockedPromotion.after.status, model.EpistemicStatus.hypothesis);

const admittedPromotion = model.tryPromotion(H1, true);
assert.equal(admittedPromotion.ok, true);
assert.equal(admittedPromotion.after.status, model.EpistemicStatus.verifiedFact);

const outwardWithoutVerification = model.tryRadialMove(H1, 0.5, false);
assert.equal(outwardWithoutVerification.ok, true);
assert.equal(outwardWithoutVerification.after.radius, 3.5);

console.log("PM-01 browser wrapper: 10 checks PASS");
