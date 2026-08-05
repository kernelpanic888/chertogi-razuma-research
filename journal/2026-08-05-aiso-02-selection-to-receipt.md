# AISO-02: the selector never becomes the executor

`AISO certificate -> CSS AdmittedTransition -> bound Receipt -> Verify -> Learn`

The bridge binds the passport, policy, observation, action field, selected action and score into one `selectionHash`. CSS independently checks its own transition contract and carries that hash into intent, receipt and witness. Learning is constructible only from a receipt that binds the same selection and passes independent `HEAD` verification.

Mutation corpus: observation drift, field drift, action substitution, payload mutation and failed verification all block the learning gate. An empty admissible set remains `NO_OP`.

Code: [formal bridge](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AISOToStewardBridge.lean) · [runtime bridge](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/aiso-steward-bridge.mjs) · [adversarial corpus](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/aiso-steward-bridge.test.mjs)

