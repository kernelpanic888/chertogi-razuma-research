# IF-BS-22F-F8C1 / Compact planar slab witness

## Русское чтение

F8B2 доказал бесконечный локальный предел на прямой. F8C1 поднимает его в честную двумерную камеру

`S = Real x [-1,1]`.

Вторая координата является компактным поперечным окном. Каждая карта действует по первой координате и сохраняет вторую:

`P_n(x,y) = (H_(a_n)(x), y)`.

Каждый относительный шаг имеет форму

`Q_n(x,y) = (T_n(x), y)`.

Возможное движение заключено в carrier

`K = [-1,1] x [-1,1]`.

В Lean доказано, что `K` компактен и что каждый `Q_n`, каждый префикс `P_n` и предельная карта `P_infinity` тождественны вне `K`.

Product metric читает расстояние как максимум расстояний по двум координатам. Вторая координата не меняется, а step constants F8B2 не меньше единицы. Поэтому подъём не увеличивает сертификаты:

`Lip(P_n) <= 3/2`,

`Lip(P_n^(-1)) <= 2`.

Прямые и обратные planar-префиксы глобально равномерно сходятся к

`P_infinity(x,y) = (H_(1/2)(x),y)`.

Для любой `ComputableBoundaryModel S` теорема F7 даёт предельный homeomorphism, actual frontier, Hausdorff-сходимость точных движущихся интерфейсов и вычислимых носителей.

## English reading

Let `S=Real x [-1,1]` and lift the one-dimensional prefixes by `P_n(x,y)=(H_(a_n)(x),y)`. The possible motion is contained in the compact carrier `K=[-1,1]x[-1,1]`. Lean verifies that every step, every prefix, and the limit are the identity outside `K`. The product lift preserves the telescopic bounds `3/2` and `2`; direct and inverse prefixes converge uniformly to `P_infinity(x,y)=(H_(1/2)(x),y)`. F7 therefore yields an actual limit frontier and Hausdorff convergence for every computable boundary model on the slab.

## Red boundary

The slab is a two-dimensional manifold with a bounded transverse coordinate, not yet the existing full Euclidean `AmbientPlane`. F8C2 must construct an explicit embedding or compactly supported extension into that plane and transport the same theorem without calling a bounded window the whole universe.
