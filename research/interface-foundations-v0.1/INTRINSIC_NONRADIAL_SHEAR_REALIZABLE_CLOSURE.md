# IF-BS-22F-F8C15: exact realizable closure

## The missing reverse inclusion

F8C14 proved that every normalized finite-chord record lies in the directional diamond

`D = {(u,s) | |u|=1 and |s|<=|u_x|+|u_y|}`

and therefore that the closure of all records is contained in `D`. F8C15 proves the converse.

## One direction, two finite endpoints

Fix a unit direction `u`, put

`w(u)=|u_x|+|u_y|`,

`p(u)=|u_x||u_y|`,

and choose a finite scale `0<t<=1`. Along the chord family define

`g_{t,u}(x) = [k(x)-k(x-tu)]/t`.

The shear kernel is continuous, hence `g_{t,u}` is continuous. At the two finite base points the values are exact:

`g_{t,u}(0)=m_t(u)`,

`g_{t,u}(tu)=-m_t(u)`,

where

`m_t(u)=w(u)-t p(u)`.

## Every strict interior slope is an actual record

If `|s|<w(u)`, choose `t>0` small enough that `|s|<m_t(u)`. Since the continuous chord-slope function takes values above and below `s`, the intermediate value theorem supplies a finite base point `x` with

`g_{t,u}(x)=s`.

Thus every strict interior point of `D` is already an actual finite-chord record, not merely a limit.

## Boundary by interior approach

For a boundary value `|s|=w(u)`, the sequence

`s_n=(1-1/(n+2))s`

lies strictly inside the same directional section and converges to `s`. Every `(u,s_n)` is realizable, so `(u,s)` belongs to the closure of realizable records.

## Exact result

Combining the F8C14 outer inclusion with the F8C15 reverse inclusion gives

`closure(actual finite-chord records) = D`.

The relaxed strip is therefore completely replaced by the exact compact realizable chamber.

## Honest boundary

The geometry of the realizable blow-up is now closed. The next open step is quantitative: transport the exact diamond chamber into the forward and inverse nonlinear certificates and compare its proved finite-mesh constants with the earlier relaxed constants. No physical interpretation follows from this equality alone.
