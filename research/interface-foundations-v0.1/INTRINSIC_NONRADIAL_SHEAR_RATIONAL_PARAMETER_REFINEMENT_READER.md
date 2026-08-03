# IF-BS-22F-F8C31A / Rational parameter refinement

## EN / Reading

F8C31A replaces the single coarse anchor by an explicit finite rational grid on the parameter square `[-1,1] x [-1,1]`, with one copy for each hemisphere. At level `n`, every coordinate is sampled at

`q_k = -1 + 2k/(n+1)`, where `0 <= k <= n+1`.

For any real coordinate `x` in `[-1,1]`, the executable choice

`k = floor((x+1)(n+1)/2)`

produces a grid coordinate satisfying

`|x-q_k| <= 2/(n+1)`.

Applying the same construction to both coordinates gives a finite node within max-distance `delta_n = 2/(n+1)`. Lean also verifies that `delta_n` tends to zero. The node stores rational coordinates and a Boolean hemisphere tag, so the parameter net is finite, serializable, and executable.

This chamber does not yet claim a net on the exact directional diamond. That requires a two-chart stereographic lift and a quantitative transport estimate; it remains the red boundary F8C31B.

## RU / Чтение

F8C31A заменяет единственную грубую опорную точку явной конечной рациональной сеткой на квадрате параметров `[-1,1] x [-1,1]`, взятой отдельно для каждого полушария. На уровне `n` каждая координата выбирается по формуле

`q_k = -1 + 2k/(n+1)`, где `0 <= k <= n+1`.

Для любой вещественной координаты `x` из `[-1,1]` исполнимый выбор

`k = floor((x+1)(n+1)/2)`

даёт узел сетки с оценкой

`|x-q_k| <= 2/(n+1)`.

Применение конструкции к обеим координатам даёт конечный узел на max-расстоянии не больше `delta_n = 2/(n+1)`. Lean также проверяет, что `delta_n` стремится к нулю. Узел хранит рациональные координаты и булеву метку полушария, поэтому параметрическая сеть конечна, сериализуема и исполнима.

Эта камера пока не заявляет сеть на точном directional diamond. Для этого нужны двухкарточный стереографический подъём и количественная оценка переноса; это красная граница F8C31B.

## Verified / Проверено

- finite rational nodes at every level;
- exact coordinate bounds in `[-1,1]`;
- floor-selected coverage radius `2/(n+1)`;
- two-coordinate max-metric coverage;
- convergence of the radius to zero.

## Open / Открыто

- two-chart surjectivity onto the exact directional diamond;
- quantitative Lipschitz transport of the parameter radius;
- an explicit exact-diamond net certificate.
