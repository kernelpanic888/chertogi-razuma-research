# IF-BS-22F-F8C3 / Nonradial elliptic twist limit

## Русское чтение

F8C3 проверяет, зависит ли предыдущая конструкция от круглой симметрии.

Берётся уже проверенное анизотропное растяжение

`A(x,y)=(2x,y)`,

его обратная карта

`A^(-1)(x,y)=(x/2,y)`,

и controlled radial twist `W_a`. Новая карта определяется сопряжением

`E_a = A o W_a o A^(-1)`.

Она действует на том же полном `AmbientPlane`, но её compact support carrier уже не круг:

`K_E = A[closedBall(0,1)]`.

Lean доказывает компактность `K_E` и точную тождественность прямой и обратной карты вне него.

Нерадиальность доказана отдельным свидетелем. Точки

`p=(2,0)` и `q=(0,2)`

имеют одинаковую евклидову норму `2`, но `p` принадлежит `K_E`, а `q` не принадлежит. Следовательно, membership в carrier нельзя определить только через евклидов радиус.

Сопряжение сохраняет точную обратимость:

`E_a^(-1)=E_(-a)`.

Из констант `Lip(A)<=2`, `Lip(A^(-1))<=1` и radial bound получается

`Lip(E_a), Lip(E_a^(-1)) <= 2(1+2|a|)`.

Для `a_n=(1/2)(1-2^(-n))` семейство `E_(a_n)` имеет единый bound `4` и глобально равномерно сходится к `E_(1/2)`. Обратные карты сходятся к `E_(-1/2)`.

Предельный homeomorphism переносит исходный actual frontier в actual frontier новой области. Точные интерфейсы и вычислимые носители сходятся к нему в Hausdorff distance.

## English reading

F8C3 tests whether the construction depends on circular symmetry. Conjugate the verified radial twist by `A(x,y)=(2x,y)` and define `E_a=A o W_a o A^(-1)`. The support carrier is the compact ellipse `A[closedBall(0,1)]`. It is provably nonradial: `(2,0)` and `(0,2)` have equal Euclidean norm, while only the first belongs to the carrier.

The inverse remains exact, `E_a^(-1)=E_(-a)`, and both directions satisfy the bound `2(1+2|a|)`. The state family `E_(a_n)` and its inverses converge uniformly to `E_(1/2)` and `E_(-1/2)`, with a common bound `4`. The limit image is an actual frontier, and both exact and computable carriers converge to it in Hausdorff distance.

## Red boundary

The nonradial geometry is produced by conjugating a radial law with a fixed coordinate deformation. This proves structural stability under a concrete loss of rotational symmetry, but it is not yet an intrinsic nonradial flow. The bound `2(1+2|a|)` is verified but intentionally coarse and is not claimed to be sharp.
