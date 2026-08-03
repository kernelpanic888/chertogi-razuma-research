# IF-BS-22F-F8C26 / Finite saturation and least global modulus

## RU

### Задача

F8C25 доказал, что точный локальный касательный модуль `L_tan(a)` ограничивает каждую конечную пару полного directional diamond. Оставалось исключить возможность меньшей глобальной константы.

### Явная последовательность

Пусть `(X,Y)` — точка, максимизирующая касательную плотность. Для `n>=0` положим

`k_n=1/(n+4)`, `r_n=sqrt(1-k_n^2)`, `sigma_n=r_n(X+Y)-2k_n`.

Два направления получаются поворотом `(X,Y)` на малые противоположные углы:

`u_n=(r_n X-k_n Y, r_n Y+k_n X)`,

`v_n=(r_n X+k_n Y, r_n Y-k_n X)`.

Склоны берутся равными `sigma_n+k_n` и `sigma_n-k_n`. Условия `k_n<=1/4`, `r_n>=3/4` обеспечивают неотрицательность склонов и включение обеих точек в directional diamond для каждого конечного `n`.

### Точная конечная геометрия

Для построенной пары

`d(p_n,q_n)=2k_n`.

Точная разность полинома факторизуется:

`|Phi_a(p_n)-Phi_a(q_n)|=A_n(a,X,Y) 2k_n`,

где

`A_n=2a[r_n Y+(X+a)sigma_n]`.

Поскольку `k_n->0`, `r_n->1` и `sigma_n->X+Y`, имеем

`A_n -> 2a[Y+(X+a)(X+Y)] = L_tan(a)`.

### Минимальность

Если `C` является любым глобальным модулем, то применение его оценки к каждой паре `(p_n,q_n)` и сокращение положительного множителя `2k_n` даёт `A_n<=C`. Переход к пределу даёт `L_tan(a)<=C`.

Вместе с верхней оценкой F8C25 получаем

`IsLeast(GlobalDiamondChordModuli(a), L_tan(a))`.

### Красная граница

Точная минимальность доказана для squared blow-up observable на directional diamond. Ещё не доказаны sharp direct/inverse constants исходной нелинейной метрики и их взаимная оптимальность.

## EN

### Problem

F8C25 proved that the exact local tangent modulus `L_tan(a)` bounds every finite pair in the full directional diamond. It remained to exclude every smaller global constant.

### Explicit sequence

Let `(X,Y)` maximize the tangent density. For `n>=0`, set

`k_n=1/(n+4)`, `r_n=sqrt(1-k_n^2)`, `sigma_n=r_n(X+Y)-2k_n`.

The two directions are opposite small rotations of `(X,Y)`:

`u_n=(r_n X-k_n Y, r_n Y+k_n X)`,

`v_n=(r_n X+k_n Y, r_n Y-k_n X)`.

Their slopes are `sigma_n+k_n` and `sigma_n-k_n`. The bounds `k_n<=1/4` and `r_n>=3/4` make both slopes nonnegative and place both points in the directional diamond for every finite `n`.

### Exact finite geometry

For this pair,

`d(p_n,q_n)=2k_n`.

The exact polynomial difference factors as

`|Phi_a(p_n)-Phi_a(q_n)|=A_n(a,X,Y) 2k_n`,

where

`A_n=2a[r_n Y+(X+a)sigma_n]`.

Since `k_n->0`, `r_n->1`, and `sigma_n->X+Y`,

`A_n -> 2a[Y+(X+a)(X+Y)] = L_tan(a)`.

### Leastness

If `C` is any global modulus, applying its inequality to every `(p_n,q_n)` and cancelling the positive factor `2k_n` gives `A_n<=C`. Passing to the limit yields `L_tan(a)<=C`.

Together with the F8C25 upper bound,

`IsLeast(GlobalDiamondChordModuli(a), L_tan(a))`.

### Red boundary

Leastness is exact for the squared blow-up observable on the directional diamond. Sharp direct/inverse constants for the original nonlinear metric, and their simultaneous optimality, remain open.
