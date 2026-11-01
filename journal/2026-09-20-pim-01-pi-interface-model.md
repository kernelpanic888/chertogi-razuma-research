# PIM-01: The Film *Pi* — What Is Between the Numbers?

## The Film *Pi* as an interface model

**Status:** Lean-checked formal interpretation · release candidate without DOI or tag<br>
**Author:** Salkutsan Aleksey<br>
**ORCID:** [0009-0006-8717-0492](https://orcid.org/0009-0006-8717-0492)
**AI assistance:** Lina Amethyst — source audit, formalization, Lean implementation, and verification

## The film

*Pi* is [Darren Aronofsky](https://www.patheos.com/blogs/filmchat/1998/08/interview-darren-aronofsky-%CF%80-1998.html)'s 1998 black-and-white psychological thriller about
the mathematician Max Cohen. Max believes that a numerical order lies beneath
the apparent chaos of nature and the financial market and that computation can
make it visible. His search brings together market data, number theory, the
game of Go, and gematria — a method of assigning numerical values to Hebrew
letters. The same chain includes the Fibonacci sequence, the golden spiral,
and Max's own changing mental state.

The film never gives a simple answer to whether Max is discovering a structure
of the world or producing and amplifying it through his method of observation,
his choice of data, and his obsession. That unresolved difference makes *Pi* a
useful model for thinking about an interface: what stands between the world,
its representation, and the meaning drawn from it by an observer.

> **Notation boundary.** *Pi* here is the film title. The number π is only one
> mathematical motif in Max's world. In the formulas below, `ρ` is our operator
> for selecting the relevant relational layer; it is not the number π.

## Result

Near the end, Max says:

> “The number is nothing. It’s the meaning. The syntax. It’s what’s between the numbers.”

The central proposal of this paper is:

> **Interface is our formal name for what Max is talking about: not the
> isolated numbers, but the selection, syntax, and relations through which
> those numbers become readable as meaning.**

This is an interpretation, not a hidden quotation. The word `interface` does
not occur in the audited film transcript, the September 1996 shooting script,
or the audited director-commentary transcript. The film gives us the line and
the research problem. The mathematics below is a separate, explicit model.

Its main thesis is conditional:

> Signs may change while meaning is preserved as an invariant of relations —
> if the transformation preserves the relations declared relevant and the two
> interpretations are aligned.

The condition matters. Without it, a change of notation may erase distinctions,
and the same visible pattern may be either world structure or a product of the
way an observer selects and encodes the world.

## Distinction: a carrier is not its meaning

Let `x` be a presented carrier: a digit string, word, graph, image, or signal.
Let `Rₓ(x)` be a relational description of that carrier: order, adjacency,
recurrence, proportion, or allowed transition. Let `ρ` select the part of that
description relevant to the question, and let `Φ` interpret it.

An interface `I` is not merely a screen. It is the whole situated operation

```text
world → observation → selection → encoding → carrier → interpretation.
```

Meaning relative to that interface is written

```text
μI(x) = Φ(ρ(Rₓ(x))).
```

This formula makes explicit the question opened by the line: perhaps the visible
number is only a carrier, while what matters lies in its syntax — in what is
*between* its signs. It does not say that every proposed pattern is real or
that every interpreter reaches the same meaning.

## Transition: when signs change

Suppose a transformation `T : X → Y` changes the representation. Digits may
become letters, a sequence may become a graph, or a signal may be encoded in a
different alphabet. We compare the relevant relational layers:

```text
ρ(Rᵧ(T(x))) = ρ(Rₓ(x)).
```

If both meanings factor through the same relational interpreter,

```text
μI(x) = Φ(ρ(Rₓ(x)))
μJ(y) = Φ(ρ(Rᵧ(y))),
```

then the formal result is

```text
μJ(T(x)) = μI(x).
```

This is not the unrestricted slogan “meaning survives translation.” It is a
commuting condition with named premises. The Lean model also records the
opposite constraint: if `T` collapses two carriers that had different meanings,
then exact semantic preservation through `T` is impossible. A lossy map can
preserve a meaning only when that meaning is constant on every fibre of the map,
that is, on the preimage of each point.

## Trace: the film as a sequence of interfaces

The opening hypothesis of *Pi* already moves through representations:

```text
nature → numbers → graph → pattern.
```

The gematria scenes make another map visible:

```text
letter → numerical value → word sum → proposed pattern.
```

Those arrows are not equivalent. A letter-by-letter encoding can retain order;
summing a word destroys order and identifies many different words. Every arrow
therefore needs its own preservation claim. Merely obtaining the same number is
not yet evidence that the same meaning has survived.

The microscope scene in the shooting script changes magnification and changes
the organization that becomes visible. The golden-rectangle sequence makes a
ratio and recursion visible under a geometric construction. The film then
extends the spiral motif across shells, fingerprints, DNA, and the galaxy. The
geometric construction supplies a precise candidate relation; the cross-scale
extension remains a character's hypothesis and a cinematic image.

Aronofsky's own accounts preserve this ambiguity. In a 1998 interview he calls
the reality or perception of the pattern the film's “big question.” In another,
he moves from a DNA spiral and a galactic spiral to the question “What's
inbetween?” and describes a search for repeating patterns at different scales.
His director's commentary and the production record also describe a visual
language constrained by Max's point of view: cuts between Max and his POV,
changes in frame rate, lens rules, and rare departures from his subjectivity.

So the film contains at least three coupled interfaces:

1. Max translates the world into numbers, diagrams, and candidate patterns.
2. Cinema translates Max's state into framing, montage, sound, and rhythm.
3. The viewer interprets both through an interface that the film itself has
   deliberately restricted.

This makes *Pi* useful not because it proves a cosmic code, but because it
dramatizes the uncertainty between discovered structure and produced structure.

## World structure and observation structure

The formal model refuses to identify those two structures.

Let `W(w)` describe a proposed structure of a world state `w`, while `I(w)` is
the carrier produced by an interface. Two world states can satisfy

```text
I(w₁) = I(w₂)
```

while still satisfying

```text
W(w₁) ≠ W(w₂).
```

The Lean module contains a concrete counterexample: a deliberately collapsing
interface presents the same carrier for two distinct Boolean world states.
Therefore observational equivalence under one interface does not entail
identity of world structure. Conversely, a pattern visible after selection
does not by itself prove that the same pattern exists independently of that
selection.

This is the exact point at which the interface reading protects the film's
ambiguity. Max may be detecting structure. He may be amplifying structure
through scale, corpus choice, memory, and selective attention. The same trace
is compatible with both accounts until additional tests discriminate them.

## State, memory, and the observer

An interface can have memory. If `hₜ` is its current state, one step can be
written

```text
xₜ = present(wₜ, hₜ)
hₜ₊₁ = update(hₜ, xₜ).
```

The next presentation then depends not only on the world but also on the
observer's accumulated state. In *Pi*, the 216-digit sequence moves from a
printout to memory; repeated attention changes which coincidences are salient;
pain and obsession alter the practical conditions of observation. This does
not reduce the film to psychology. It simply prevents “the observer” from
being treated as a transparent, stateless window.

## Formal trace in TLFL

The model is implemented in Lean 4 against the canonical `TMI.Library`:

- [`PiInterfaceModel.lean`](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/8cc0d188b4ede393ca2957877eb4bc98f2b23d2a/lean/TMI/InterfaceMathematics/PiInterfaceModel.lean)
- [`PiInterfaceModelAudit.lean`](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/8cc0d188b4ede393ca2957877eb4bc98f2b23d2a/lean/TMI/InterfaceMathematics/PiInterfaceModelAudit.lean)
- [claim and reproduction note](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/8cc0d188b4ede393ca2957877eb4bc98f2b23d2a/research/pi-interface-model-v0.1/README.md)
- [audit record](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/8cc0d188b4ede393ca2957877eb4bc98f2b23d2a/research/pi-interface-model-v0.1/AUDIT.md)

Targeted verification with Lean `4.31.0-rc1` completed 54 build jobs. The source
contains no `sorry`, `admit`, or `sorryAx`. A separate audit carrier checks ten
named declarations; Lean reports that all ten depend on no axioms.

The principal theorem is
`meaning_preserved_of_common_factorization`. Additional checked results cover
semantic commutation, invariance under composition, the necessary fibre
condition for lossy maps, world/observation separation, state and memory, and a
toy change of alphabet whose selected relational code is preserved.

## Claim boundary

The formalization proves a conditional implication inside the declared model.
It does **not** prove that:

- *Pi* discovered a hidden numerical code of nature;
- Aronofsky used the word `interface` or asserted this formalism;
- the selected relation `R` is objective, unique, or observer-independent;
- gematria preserves semantic content;
- structural isomorphism alone determines interpretation;
- every translation or change of representation preserves meaning;
- a repeating pattern across selected examples establishes a law of nature.

The quotations establish coordinates in the film and interviews. The
interpretation connects those coordinates. Lean checks the consequences of
the stated premises. These are three different epistemic acts.

## Return

The line “what's between the numbers” can now be stated without mystification.
In the model, the number is treated as carrier `x`. What is between its signs is
modeled as the
selected relational structure `ρ(Rₓ(x))`. The interface `I` determines how a
world is observed, selected, encoded, and interpreted. A representation change
`T` preserves meaning only when the relevant structure and interpretation make
the required diagram commute.

So yes: **interface is what Max is talking about — in our formal vocabulary.**
The qualification does not weaken the idea. It makes the idea inspectable.

## Source coordinates

- [Bilingual interactive reader](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/pi-interface-model/).
- [Public discussion on LinkedIn](__LINKEDIN_POST_URL__).
- Darren Aronofsky, *Pi* (1998), quoted line at approximately
  `01:12:34–01:12:48` in the audited English subtitle track.
- [Shooting script, September 1996](https://imsdb.com/scripts/Pi.html).
- [Peter T. Chattaway interview, 1998](https://www.patheos.com/blogs/filmchat/1998/08/interview-darren-aronofsky-%CF%80-1998.html).
- [Combustible Celluloid interview, 25 June 1998](https://www.combustiblecelluloid.com/daint.shtml).
- [Director-commentary transcript](https://secondtrack.org/commentary/pi-1998).
- [American Cinematographer production account, April 1998](https://theasc.com/article/pi-numerical-delusions/).
