# HMR-01 / Human Mathematical Reader Contract

A public reader is written first for a human eye. Formal code remains the
verifiable foundation, but it is not the default visual language of the reading
surface.

## Visible mathematical layer

1. Display mathematics uses semantic mathematical notation (native MathML in
   the self-contained site), not Lean syntax or a screenshot of code.
2. Every symbol is introduced in prose before its first substantial formula.
3. The main logical movement is shown as a small number of centred equations;
   implementation syntax is linked as evidence instead of copied into the main
   narrative.
4. A claim boundary is written in ordinary language next to the mathematics.
5. Formal status is explicit: theorem, model bridge, empirical observation, or
   open seam must not be visually collapsed into one another.

## Formal foundation

Lean, executable tests, source commits, and audits remain canonical whenever
they exist. A reader links to them through provenance. If no formal carrier
exists yet, the reader says `OPEN SEAM`; it does not imitate a proof by styling
mathematical prose as code.

## Accessibility

- Equations use semantic MathML with an accessible label.
- Explanatory text remains at least 16px on narrow screens.
- Meaning never depends on colour alone.
- Animation and interaction are optional to comprehension.

The goal is not to make the mathematics less exact. It is to stop asking the
reader to parse a programming language before they are allowed to see the idea.
