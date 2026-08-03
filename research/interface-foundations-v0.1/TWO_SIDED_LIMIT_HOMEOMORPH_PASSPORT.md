# Паспорт IF-BS-22F-F7

## Точка маршрута

`IF-BS-22F-F7 / TWO-SIDED PREFIX LIMIT -> HOMEOMORPH -> ACTUAL FRONTIER`

## Вход

- Полное метрическое пространство `X`.
- Controlled-префиксы `F_n : X ≃ X` и обратные карты `G_n = F_n^{-1}`.
- Uniform-Cauchy сходимость `F_n` и `G_n` на всём `X`.
- Единые границы `Lip(F_n) <= L` и `Lip(G_n) <= M`.
- `ComputableBoundaryModel` с `I = frontier(A)`.

## Выход

- Существуют равномерные пределы `F_infinity` и `G_infinity`.
- `G_infinity o F_infinity = id` и `F_infinity o G_infinity = id`.
- `H_infinity = (F_infinity, G_infinity)` является homeomorphism.
- `frontier(H_infinity[A]) = H_infinity[I]`.
- `d_H(F_n[I], H_infinity[I]) -> 0`.
- `d_H(K_n^(n), H_infinity[I]) -> 0`.

## Проверяемая формула

`UniformCauchy(F_n) + UniformCauchy(F_n^{-1}) + sup Lip(F_n) < infinity + sup Lip(F_n^{-1}) < infinity`

`=> exists H_infinity : X homeomorphic X`

`=> frontier(H_infinity[A]) = H_infinity[frontier(A)]`.

## Красная граница

Это theorem of passage, а не существование конкретной динамики. Нужен явный нетривиальный infinite sequence controlled-шагов с суммируемыми смещениями и проверенными двусторонними bounds.

## Русская вычитка

Если каждый конечный маршрут обратим, прямые и обратные маршруты равномерно стабилизируются на всём пространстве, а их чувствительность не растёт без границы, то обратимость не исчезает в пределе. Возникает единое предельное преобразование пространства, и общий носитель F6 становится настоящей границей предельной внутренней области.

## Следующий шаг по паспорту

`IF-BS-22F-F8`: построить конкретное infinite family компактно поддержанных controlled-деформаций с суммируемыми амплитудами, доказать global uniform-Cauchy прямых и обратных префиксов и получить первый нетривиальный verified limit homeomorphism как свидетель применимости F7.
