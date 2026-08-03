# IF-BS-22F-F8C5 / Exact support closure of the intrinsic shear

## Русское чтение

Берём уже построенный внутренний сдвиг

[
S_a(x,y)=igl(x,;y+a,arphi(x)arphi(y)igr),
qquad
arphi(t)=max(0,1-|t|).
]

При любом (a>0) точка движется тогда и только тогда, когда одновременно
(|x|<1) и (|y|<1). Поэтому множество реально движущихся точек и его
минимальный замкнутый носитель имеют точную форму

[
operatorname{Move}(S_a)=(-1,1)^2,
qquad
overline{operatorname{Move}(S_a)}=[-1,1]^2.
]

Фронтир носителя теперь не круговая защитная оболочка, а ровно четыре ребра:

[
partial[-1,1]^2=
([-1,1]	imes{-1,1})cup({-1,1}	imes[-1,1]).
]

Доказана минимальность: если замкнутое множество (K) содержит всё возможное
движение в том смысле, что (S_a(p)=p) для каждого (p
otin K), то
([-1,1]^2subseteq K).

Метрическая оценка ядра улучшена с безопасного коэффициента (2) до
евклидова коэффициента (sqrt2):

[
|kappa(p)-kappa(q)|le sqrt2,d(p,q).
]

Отсюда следуют

[
(1-sqrt2,a)d(p,q)
le d(S_a p,S_a q)
le(1+sqrt2,a)d(p,q).
]

Для (0le ale	frac14) зазор (1-sqrt2a) положителен, а обе стороны
эквивалентности контролируются общей константой

[
C(a)=rac1{1-sqrt2a}.
]

На вертикальной оси получены точные одномерные нижние границы: никакая прямая
глобальная константа не может быть меньше (1+a), а никакая обратная не может
быть меньше ((1-a)^{-1}).

## English reading

For every (a>0), the intrinsic shear moves exactly the open square
((-1,1)^2). Its minimal closed carrier is the closed square ([-1,1]^2),
and its frontier is exactly the union of the four square edges.

The kernel estimate is sharpened from the previous safe coefficient (2) to
the Euclidean coefficient (sqrt2), giving two-sided metric control and the
common direct/inverse envelope (C(a)=(1-sqrt2a)^{-1}) for
(0le ale 1/4).

The vertical fibers also certify the exact one-dimensional lower bounds
(1+a) and ((1-a)^{-1}).

## Honest boundary

The exact support, its frontier, its minimality, the (sqrt2) envelope, and
the axial lower bounds are formal theorems. The globally optimal spectral
constant of the full two-dimensional map is not yet identified. No physical
Planck scale is inferred from this computational carrier.
