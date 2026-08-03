# IF-BS-22F-F8C23 / Intrinsic nonradial shear: finite-chord bridge

## RU

### Задача

F8C22 вычислил точный локальный касательный модуль, но локальная производная сама по себе не является глобальной оценкой для двух конечных точек. F8C23 строит отдельный сертифицированный мост к хордовой метрике точного реализуемого ромба.

### Конечная разность

Для точки `p=(u,s)` реализуемого ромба, где `u=(x,y)` лежит на единичной окружности,

`Phi_a(p) = x^2 + (y + a s)^2 = 1 + 2 a s y + a^2 s^2`.

Поэтому для двух конечных точек `p,q`

`Phi_a(p)-Phi_a(q) = 2a(s_p y_p-s_q y_q) + a^2(s_p^2-s_q^2)`.

Используются только уже доказанные ограничения точного ромба:

`|s| <= sqrt(2)`, `|y| <= 1`, `|Delta y| <= d(p,q)`, `|Delta s| <= d(p,q)`.

Отсюда формально получено

`|Phi_a(p)-Phi_a(q)| <= G(a) d(p,q)`,

где

`G(a) = 2a(sqrt(2)+1) + 2 sqrt(2) a^2`, `a >= 0`.

Это глобальное утверждение для каждой конечной пары точек точного реализуемого ромба.

### Связь с F8C22

Точный локальный модуль удовлетворяет

`L_tan(a) <= G(a)`.

Разность `Gamma_chord(a)=G(a)-L_tan(a)` неотрицательна и записывает честный бюджет перехода от локального касания к конечной хорде.

При `a=1/2`

`G(1/2)=1+(3/2)sqrt(2)`.

F8C22 сохраняет точное значение `L_tan(1/2)` через сертифицированный корень стационарного уравнения.

### Красная граница

`G(a)` доказан как достаточный глобальный модуль. Не доказано, что он является наименьшим глобальным хордальным модулем. Равенство `Gamma_chord(a)=0` также не заявлено.

## EN

### Problem

F8C22 computed the exact local tangent modulus, but a local derivative is not by itself a global estimate for two finite points. F8C23 builds a separate certified bridge to the chord metric of the exact realizable diamond.

### Finite difference

For a realizable-diamond point `p=(u,s)` with `u=(x,y)` on the unit circle,

`Phi_a(p) = x^2 + (y + a s)^2 = 1 + 2 a s y + a^2 s^2`.

Hence, for two finite points `p,q`,

`Phi_a(p)-Phi_a(q) = 2a(s_p y_p-s_q y_q) + a^2(s_p^2-s_q^2)`.

Using only the already verified exact-diamond constraints

`|s| <= sqrt(2)`, `|y| <= 1`, `|Delta y| <= d(p,q)`, `|Delta s| <= d(p,q)`,

Lean proves

`|Phi_a(p)-Phi_a(q)| <= G(a) d(p,q)`,

where

`G(a) = 2a(sqrt(2)+1) + 2 sqrt(2) a^2`, `a >= 0`.

This is a global statement for every finite pair in the exact realizable diamond.

### Link to F8C22

The exact local modulus satisfies

`L_tan(a) <= G(a)`.

The nonnegative difference `Gamma_chord(a)=G(a)-L_tan(a)` is an honest uncertainty budget for the passage from local touch to a finite chord.

At `a=1/2`,

`G(1/2)=1+(3/2)sqrt(2)`.

F8C22 retains the exact value of `L_tan(1/2)` through its certified stationary root.

### Red boundary

`G(a)` is proved sufficient, not least. No claim is made that the global chord modulus equals `G(a)` or that `Gamma_chord(a)=0`.

