# IF-BS-22F-F8C14: realizable blow-up outer hull

## Why F8C13 was deliberately conservative

F8C13 used the compact relaxed chamber

`S^1 x [-sqrt(2),sqrt(2)]`.

It is safe, but it allows the extreme slope `sqrt(2)` at every direction. Actual chords carry more information: the maximal slope depends on their normalized direction.

## Directed diamond inequality

For every nonzero chord, let

`u=(p-q)/dist(p,q)`

and

`s=(k(p)-k(q))/dist(p,q)`.

The formal result proves

`|s| <= |u_x|+|u_y|`.

Hence every actual record belongs to the directional diamond band

`D = {(u,s) | |u|=1 and |s|<=|u_x|+|u_y|}`.

The band `D` is closed and compact. Therefore

`closure(actual finite-chord records) subset D`.

## What disappears

For a vertical direction, the diamond permits only `|s|<=1`. The relaxed points `(vertical,+/-sqrt(2))` are outside `D`, so they cannot even be limits of finite chord records.

This proves that both exact relaxed poles from F8C13 are computational safety poles, not intrinsic chord poles.

## What is actually reached

For every nonnegative unit direction `(x,y)`, the boundary record

`((x,y),x+y)`

is the limit of explicit finite chords approaching the kernel origin. In particular, diagonal directions reach slope `sqrt(2)`.

The global `sqrt(2)` kernel constant is therefore real, but it lives on diagonal directions rather than on every direction.

## Honest boundary

F8C14 proves a closed outer hull and one complete boundary arc. It does not yet prove that every interior record in `D`, or every sign-reflected boundary arc, belongs to the closure. Equality between the realizable closure and `D` remains the next theorem.
