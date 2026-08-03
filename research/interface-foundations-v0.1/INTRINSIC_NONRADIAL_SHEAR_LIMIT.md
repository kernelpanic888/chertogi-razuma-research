# IF-BS-22F-F8C4 / Intrinsic nonradial shear limit

## Русское чтение

F8C4 строит нерадиальную compact-support деформацию без внешнего растяжения координат.

Пусть

`phi(t)=max(0,1-|t|)`

и

`S_a(x,y)=(x, y+a phi(x) phi(y))`.

Первая координата сохраняется. На каждой вертикальной прямой вторая координата проходит через одномерную tent-карту

`y -> y + b phi(y)`, где `b=a phi(x)`.

При `0<=a<=1/4` имеем `0<=b<1`. Уже проверенные strict monotonicity и surjectivity tent-карты дают биективность каждого fiber, а значит и всей двумерной карты.

Kernel `phi(x)phi(y)` имеет global Lipschitz bound `2`. Поэтому

`dist(S_a(p),S_a(q)) <= (1+2a) dist(p,q)`

и

`(1-2a) dist(p,q) <= dist(S_a(p),S_a(q))`.

Из второй оценки следует Lipschitz-контроль обратной карты. Для `0<=a<=1/4` обе стороны можно записать одной near-identity константой

`Lip(S_a), Lip(S_a^(-1)) <= 1+4a`.

При `a->0` эта константа стремится к `1`. Это устраняет грубый постоянный множитель сопряжения из F8C3.

Карта тождественна вне доказанного compact carrier `closedBall(0,2)`. Этот carrier честно является внешней защитной оболочкой; минимальное множество движения меньше и имеет square-like геометрию.

Нерадиальность доказана без смены координат. Точки `(1/2,0)` и `(0,1/2)` имеют одинаковую норму, но при `a=1/4` квадраты норм их образов равны `17/64` и `25/64`.

Для `a_n=(1/4)(1-2^(-n))` direct family сходится глобально равномерно к `S_(1/4)`. Co-Lipschitz bound даёт глобальную равномерную сходимость обратных карт. Предельный образ интерфейса является actual frontier, а точные и вычислимые носители сходятся к нему в Hausdorff distance.

## English reading

F8C4 defines the intrinsic triangular deformation `S_a(x,y)=(x,y+a phi(x)phi(y))`, with `phi(t)=max(0,1-|t|)`. No external coordinate conjugation is used. Fiberwise tent-homeomorphisms prove bijectivity. The kernel is globally 2-Lipschitz, yielding direct and co-Lipschitz estimates. For `0<=a<=1/4`, both directions are controlled by the near-identity constant `1+4a`.

The map is exactly fixed outside the compact carrier `closedBall(0,2)`. Equal-norm probes `(1/2,0)` and `(0,1/2)` acquire different output norms, proving intrinsic loss of rotational symmetry. The canonical family and its inverses converge uniformly to `S_(1/4)` and its inverse. The limit image is an actual frontier, and exact and computable carriers converge to it in Hausdorff distance.

## Red boundary

The compact ball of radius `2` is a verified carrier, not the minimal support. The exact square-like support geometry and sharper optimal constants are not claimed here. No physical interpretation of the shear direction or amplitude is inferred.
