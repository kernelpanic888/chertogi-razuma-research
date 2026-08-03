# IF-BS-22F-F8B1 / Compact tent homeomorphism

## Русское чтение

F8A показал нетривиальный обратимый предел, но двигал всю прямую. F8B1 строит один полностью локальный шаг.

Берём треугольный профиль

`phi(x) = max(0, 1 - |x|)`

и карту

`H_a(x) = x + a phi(x)`, где `0 <= a < 1`.

Профиль равен нулю при `|x| >= 1`, поэтому `H_a(x)=x` вне `[-1,1]`. Внутри носителя левая ветвь имеет наклон `1+a`, правая ветвь имеет наклон `1-a`. Условие `a<1` не даёт правой ветви схлопнуться или изменить ориентацию.

В Lean доказано:

`Lip(H_a) <= 1+a`,

`(1-a)d(x,y) <= d(H_a(x),H_a(y))`,

`Lip(H_a^(-1)) <= 1/(1-a)`.

Карта строго возрастает, непрерывна и сюръективна, поэтому задаёт homeomorphism всей вещественной прямой. Это уже настоящий compactly supported controlled step, а не глобальная калибровочная трансляция.

## English reading

Let `phi(x)=max(0,1-|x|)` and `H_a(x)=x+a phi(x)` for `0<=a<1`. The map is exactly the identity for `|x|>=1`. Its left and right interior slopes are `1+a` and `1-a`, so it remains strictly increasing and surjective. Lean verifies the forward bound `Lip(H_a)<=1+a`, the co-Lipschitz estimate `(1-a)d(x,y)<=d(H_a(x),H_a(y))`, and the inverse bound `Lip(H_a^(-1))<=1/(1-a)`. Thus `H_a` is a controlled homeomorphism with compact support.

## Red boundary

F8B1 certifies one local parameterized deformation. It does not yet construct the infinite summable sequence or prove that its prefixes converge to a local limit homeomorphism. That is the separate obligation F8B2.
