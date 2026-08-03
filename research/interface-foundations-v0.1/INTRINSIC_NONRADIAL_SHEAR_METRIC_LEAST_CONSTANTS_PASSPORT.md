# Паспорт IF-BS-22F-F8C27

## Имя

Least direct and inverse metric constants / Наименьшие прямые и обратные метрические константы.

## Вход

- Sharp diamond extrema F8C17.
- Exact forward/inverse spectral metric bounds и конечные контрпробы.
- Least variation modulus F8C26 для отделения вариационной и экстремальной задач.

## Новые доказанные узлы

- `exactDiamondUpperSq(a)=forwardSpectralSq(a)`.
- `exactDiamondLowerSq(a) inverseSpectralSq(a)=1` при `0<=a<1`.
- `exactDirectMetricConstant(a)=sqrt(exactDiamondUpperSq(a))`.
- `exactInverseMetricConstant(a)=1/sqrt(exactDiamondLowerSq(a))`.
- Прямой `IsLeast` среди всех неотрицательных глобальных metric bounds.
- Обратный `IsLeast` среди всех неотрицательных глобальных backward bounds.
- Одновременная минимальность обеих констант.

## Статус утверждения

Для intrinsic nonlinear shear и `0<=a<1` точные глобальные direct/inverse metric constants полностью определены и одновременно минимальны.

## Проверяемый носитель

- `formal/IntrinsicNonradialShearMetricLeastConstants.lean`
- `formal/IntrinsicNonradialShearMetricLeastConstantsAudit.lean`

## Красная граница

Теория знает sharp constants при известном `a`, но ещё не даёт конечный робастный сертификат восстановления `a` из зашумлённых измерений.

## Следующий шаг

IF-BS-22F-F8C28: finite noisy identifiability chamber для параметра `a`.
