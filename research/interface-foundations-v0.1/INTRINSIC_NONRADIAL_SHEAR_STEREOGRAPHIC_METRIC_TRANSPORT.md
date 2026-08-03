# IF-BS-22F-F8C31C: Stereographic metric transport

## Status

Formally closed in Lean. The result concerns the exact directional diamond of the current mathematical model; it is not an empirical claim about physical spacetime.

## Statement

For one stereographic chart let

`G(t1,v1,t2,v2) = max(|t1-t2|, |v1-v2|)`.

On `t1,t2,v1,v2 in [-1,1]`, the two-chart lift `L` satisfies

`dist(L(h,t1,v1), L(h,t2,v2)) <= 10 G(t1,v1,t2,v2)`.

The rational parameter grid from F8C31A has radius `2/(n+1)`. Its stereographic image therefore covers the entire exact directional diamond with radius

`Delta_n = 20/(n+1) -> 0`.

## Error budget

- Each rational circle coordinate changes by at most `4|t1-t2|`.
- The ambient direction changes by at most `8|t1-t2|`.
- The signed slope changes by at most `8|t1-t2| + 2|v1-v2|`.
- The product metric is therefore bounded by `10 G`.

## What is now proved

At every refinement level there is a finite set of actual points of the exact diamond. Every exact-diamond point lies within `20/(n+1)` of one of those finite points, and the radius tends to zero.

## Red boundary

The finite points are mathematically computable, but this step does not yet serialize them as a public measurement table or connect each row to the certificate pipeline.

---

# IF-BS-22F-F8C31C: Метрический перенос стереографической сетки

## Статус

Формально замкнуто в Lean. Результат относится к точному направленному ромбу текущей математической модели и не является эмпирическим утверждением о физическом пространстве-времени.

## Формулировка

Для одной стереографической карты положим

`G(t1,v1,t2,v2) = max(|t1-t2|, |v1-v2|)`.

При `t1,t2,v1,v2 in [-1,1]` двухкартовый подъём `L` удовлетворяет оценке

`dist(L(h,t1,v1), L(h,t2,v2)) <= 10 G(t1,v1,t2,v2)`.

Рациональная параметрическая сетка F8C31A имеет радиус `2/(n+1)`. Поэтому её стереографический образ покрывает весь точный направленный ромб с радиусом

`Delta_n = 20/(n+1) -> 0`.

## Бюджет ошибки

- Каждая рациональная координата окружности меняется не более чем на `4|t1-t2|`.
- Направление в окружающем пространстве меняется не более чем на `8|t1-t2|`.
- Подписанный наклон меняется не более чем на `8|t1-t2| + 2|v1-v2|`.
- Поэтому метрика произведения ограничена величиной `10 G`.

## Что теперь доказано

На каждом уровне уточнения существует конечное множество настоящих точек точного ромба. Каждая точка ромба лежит не далее `20/(n+1)` от одной из них, а этот радиус стремится к нулю.

## Красная граница

Точки математически вычислимы, но на этом шаге они ещё не сериализованы в публичную таблицу измерений и не связаны построчно с конвейером сертификатов.
