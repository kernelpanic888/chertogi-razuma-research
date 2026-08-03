# Паспорт IF-BS-22F-F8C30

## Имя

Executable rational coarse net / Исполнимая рациональная грубая сеть.

## Вход

- Raw finite sample transport F8C29.
- Exact directional diamond.
- Product metric on BlowUpPoint.
- F8C28 certified identifiability interval.

## Новые доказанные узлы

- Рациональный anchor c0=((1,0),0).
- Доказанная принадлежность c0 exact diamond.
- Глобальная оценка D subset Ball(c0,2).
- Явная singleton delta0=2 сеть.
- RationalMeasurementRecord с Repr и DecidableEq.
- Исполнимый Boolean shape checker.
- Точные forward/inverse readings, равные 1.
- Сквозной theorem: executable sample -> F8C29 -> F8C28 interval.

## Статус утверждения

Впервые существует полностью явный и машинно исполнимый reference certificate без скрытых coverage или measurement assumptions. Его точность намеренно груба.

## Проверяемый носитель

- `formal/IntrinsicNonradialShearExecutableCoarseNet.lean`
- `formal/IntrinsicNonradialShearExecutableCoarseNetAudit.lean`

## Красная граница

Нужна refinement family с delta_n->0 и внешний parser/serializer.

## Следующий шаг

IF-BS-22F-F8C31: rational stereographic refinement family.
