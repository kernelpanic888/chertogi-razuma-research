# IF-BS-22F-F8C25 / Actual-pair transport

## RU

### Задача

F8C24 точно оптимизировал абстрактную центрированную камеру, но не доказал, что каждая настоящая конечная пара реализуемого ромба входит в неё без потерь. F8C25 строит это отображение и переносит точную локальную крышу на все конечные пары.

### Каноническая запись

Для двух единичных направлений `u` и `v` вводятся `m=(u+v)/2` и `h=(u-v)/2`. Единичность концов немедленно даёт

`m·h=0`, `||m||^2+||h||^2=1`.

Положим `r=||m||`, `k=||h||`. Тогда `r^2+k^2=1`. При `k>0` канонические абсолютные координаты выбираются как

`X=|h_y|/k`, `Y=|h_x|/k`.

Ортогональность даёт точные тождества

`|m_x|=rX`, `|m_y|=rY`, `|h_x|=kY`, `|h_y|=kX`.

Случай `k=0` выделен отдельно: направления совпадают, `r=1`, а `(X,Y)=(|m_x|,|m_y|)`. Антиподальный случай не исключается: там `r=0`, `k=1`.

### Точная средняя ширина

Одномерное тождество

`|m+h|+|m-h|=2 max(|m|,|h|)`

превращает средние абсолютные координаты двух концов в

`W=max(rX,kY)+max(rY,kX)`.

Поэтому средний склон `σ=(s_1+s_2)/2` удовлетворяет `|σ|<=W` без грубой суммы координат.

### Перенос конечной разности

Для `δ=(s_1-s_2)/2` разность точного полинома имеет форму

`ΔΦ=4a[σh_y+δ(m_y+aσ)]`.

Метрика произведения даёт `2k<=d` и `2|δ|<=d`. После подстановки канонической записи получается

`|ΔΦ| <= 2ad C_a(X,Y,r,k) <= 2ad E(a)`.

Следовательно, на полном реализуемом ромбе

`|Φ_a(p)-Φ_a(q)| <= L_tan(a) d(p,q)`,

где `L_tan(a)=2aE(a)`. Положительная поправка F8C23 для глобальной верхней оценки не нужна.

### Красная граница

F8C25 доказывает достаточность `L_tan(a)` для всех конечных пар, но ещё не доказывает его минимальность среди всех глобальных модулей. Для этого нужна явная последовательность допустимых конечных пар, чей quotient стремится к касательному свидетелю и насыщает все промежуточные ограничения.

## EN

### Problem

F8C24 exactly optimized the abstract centered chamber but did not prove that every actual finite pair in the realizable diamond enters it losslessly. F8C25 constructs that map and transports the exact local roof to all finite pairs.

### Canonical record

For two unit directions `u` and `v`, set `m=(u+v)/2` and `h=(u-v)/2`. Unit endpoints immediately imply

`m·h=0`, `||m||^2+||h||^2=1`.

Let `r=||m||` and `k=||h||`; then `r^2+k^2=1`. For `k>0`, choose canonical absolute coordinates

`X=|h_y|/k`, `Y=|h_x|/k`.

Orthogonality gives the exact identities

`|m_x|=rX`, `|m_y|=rY`, `|h_x|=kY`, `|h_y|=kX`.

The `k=0` branch is explicit: the directions coincide, `r=1`, and `(X,Y)=(|m_x|,|m_y|)`. The antipodal case remains included, with `r=0`, `k=1`.

### Exact averaged width

The one-dimensional identity

`|m+h|+|m-h|=2 max(|m|,|h|)`

turns the averaged endpoint coordinates into

`W=max(rX,kY)+max(rY,kX)`.

Hence the mean slope `σ=(s_1+s_2)/2` satisfies `|σ|<=W` without a coarse coordinate sum.

### Finite-difference transport

With `δ=(s_1-s_2)/2`, the exact polynomial difference is

`ΔΦ=4a[σh_y+δ(m_y+aσ)]`.

The product metric gives `2k<=d` and `2|δ|<=d`. Substituting the canonical record yields

`|ΔΦ| <= 2ad C_a(X,Y,r,k) <= 2ad E(a)`.

Therefore, throughout the full realizable diamond,

`|Φ_a(p)-Φ_a(q)| <= L_tan(a) d(p,q)`,

where `L_tan(a)=2aE(a)`. The positive F8C23 correction is unnecessary for the global upper bound.

### Red boundary

F8C25 proves that `L_tan(a)` is sufficient for every finite pair, but not yet that it is the least global modulus. That requires an explicit admissible finite-pair sequence whose quotient converges to the tangent witness while saturating every intermediate constraint.

