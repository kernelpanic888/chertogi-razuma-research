# IF-BS-22F-F8C2B / Controlled radial-twist limit

## Русское чтение

F8C2B превращает compact radial twist из одного homeomorphism в управляемую бесконечную историю на полной евклидовой плоскости.

Для обычного вращения сначала доказано точное сохранение расстояния:

`dist(R_theta(p),R_theta(q)) = dist(p,q)`.

Из стандартных оценок синуса и косинуса следует угловая оценка

`dist(R_alpha(p),R_beta(p)) <= 2 |alpha-beta| norm(p)`.

Радиальный профиль `max(0,1-r)` является 1-Lipschitz. Поэтому для

`W_a(p)=R_(a max(0,1-norm(p)))(p)`

получен глобальный bound

`dist(W_a(p),W_a(q)) <= (1+2|a|) dist(p,q)`.

Точная обратная карта есть `W_(-a)`, поэтому тот же bound действует в обратную сторону. Так каждый radial twist становится `ControlledEquiv`.

Далее берётся амплитуда

`a_n = (1/2)(1-2^(-n))`

и шаг

`delta_n = a_(n+1)-a_n`.

Последовательность состоит из малых поворотов `W_(delta_n)`. Сохранение радиуса даёт точное телескопирование:

`W_(delta_(n-1)) o ... o W_(delta_0) = W_(a_n)`.

Накопленные прямые и обратные константы не превосходят `exp(1)`. Это следует из `1+x <= exp(x)` и суммы шагов `a_n <= 1/2`.

Префиксы и их обратные глобально равномерно сходятся к `W_(1/2)` и `W_(-1/2)`. Теорема F7 поэтому применима на полном `AmbientPlane`: предельный образ интерфейса является настоящей границей предельной области, а точные и вычислимые носители сходятся к ней в Hausdorff distance.

Вся история и предел тождественны вне компактного единичного диска.

## English reading

F8C2B upgrades the compact radial twist to a controlled infinite history on the full Euclidean plane. Rotation is an isometry, angle variation is bounded by `2|alpha-beta| norm(p)`, and the radial tent profile is 1-Lipschitz. Hence `W_a` has the global two-sided bound `1+2|a|` and defines a `ControlledEquiv`.

With `a_n=(1/2)(1-2^(-n))` and `delta_n=a_(n+1)-a_n`, the small twists telescope exactly to `W_(a_n)`. Both accumulated constants are bounded by `exp(1)`. The forward and inverse prefixes converge uniformly to `W_(1/2)` and `W_(-1/2)`. F7 then yields the actual frontier of the limit region and Hausdorff convergence of both exact and computable carriers. Every map remains exactly fixed outside the compact unit disk.

## Red boundary

This is a verified mathematical deformation model. It does not identify the radial parameter with physical time, energy, gravity, or a measured Planck-scale quantity. Those interpretations require a separate empirical bridge.
