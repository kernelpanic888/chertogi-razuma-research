# IF-BS-22F-F8C24 / Centered two-point envelope

## RU

### Задача

F8C23 дал достаточную глобальную крышу `G(a)`, но оставил положительный бюджет между ней и точным локальным модулем. F8C24 отделяет чистую двухточечную геометрию от грубых поэлементных оценок и точно оптимизирует центрированную скалярную камеру.

### Центрированные координаты

Абсолютное направление среднего задаётся первой единичной парой

`X >= 0`, `Y >= 0`, `X^2+Y^2=1`.

Размеры среднего и полухорды задаются второй единичной парой

`r >= 0`, `k >= 0`, `r^2+k^2=1`.

После точной оценки среднего допустимого склона возникает ширина

`W=max(rX,kY)+max(rY,kX)`.

Центрированная двухточечная огибающая равна

`C_a(X,Y,r,k)=rY+(X+a)W`.

### Четыре режима

Два максимума дают четыре ветви.

- Обе `r`-ветви: выражение сжимается множителем `r<=1` и лежит под локальным профилем в той же точке `(X,Y)`.
- Обе `k`-ветви: используется `k<=1`; результат снова лежит под тем же локальным профилем.
- Смешанная `X`-ветвь: используется `r+k<=sqrt(2)` и диагональная точка `(1/sqrt(2),1/sqrt(2))`.
- Смешанная `Y`-ветвь: используется `2XY<=1` и та же диагональная точка.

Lean доказывает для всех четырёх ветвей

`C_a(X,Y,r,k) <= E(a)`.

### Точный максимум

При `r=1`, `k=0` центрированная огибающая возвращается к локальному профилю. В точке `tangentEnvelopePoint(a)` достигается равенство

`C_a=E(a)`.

Следовательно, `E(a)` является точным наибольшим значением всей центрированной камеры. Положительная поправка F8C23 не является внутренним свойством этой скалярной оптимизации.

### Красная граница

Ещё не формализовано каноническое отображение каждой реальной пары точек реализуемого ромба в центрированные координаты с сохранением всех ограничений. Поэтому равенство между наименьшим глобальным хордальным модулем и `L_tan(a)=2aE(a)` пока не заявлено.

## EN

### Problem

F8C23 supplied a sufficient global roof `G(a)` but left a positive budget above the exact local modulus. F8C24 separates the pure two-point geometry from termwise coarse estimates and exactly optimizes the centered scalar chamber.

### Centered coordinates

The absolute midpoint direction is represented by a first unit pair

`X >= 0`, `Y >= 0`, `X^2+Y^2=1`.

The midpoint and half-chord radii form a second unit pair

`r >= 0`, `k >= 0`, `r^2+k^2=1`.

The exact averaged slope width is bounded by

`W=max(rX,kY)+max(rY,kX)`.

The centered two-point envelope is

`C_a(X,Y,r,k)=rY+(X+a)W`.

### Four regimes

The two maxima produce four branches.

- Both `r` branches contract by `r<=1` and stay below the local profile at `(X,Y)`.
- Both `k` branches use `k<=1` and again stay below the same local profile.
- The mixed `X` branch uses `r+k<=sqrt(2)` and the diagonal point `(1/sqrt(2),1/sqrt(2))`.
- The mixed `Y` branch uses `2XY<=1` and the same diagonal point.

Lean proves in every branch

`C_a(X,Y,r,k) <= E(a)`.

### Exact optimum

At `r=1`, `k=0`, the centered envelope returns to the local profile. At `tangentEnvelopePoint(a)` it attains

`C_a=E(a)`.

Thus `E(a)` is the exact greatest value of the entire centered chamber. The positive F8C23 correction is not intrinsic to this scalar optimization.

### Red boundary

The canonical transport of every actual realizable-diamond pair into these centered coordinates, with all constraints preserved, is not yet formalized. Equality between the least global chord modulus and `L_tan(a)=2aE(a)` is therefore not yet claimed.

