# Паспорт IF-BS-22F-F8C31A

## Имя

Rational parameter refinement / Рациональное уточнение параметров.

## Вход

- Executable singleton certificate F8C30.
- FloorSemiring для вещественного nearest-grid алгоритма.
- Рациональное кодирование и точный Real decode.

## Новые доказанные узлы

- Явные rational nodes q_k=-1+2k/(n+1).
- Finite-index representation через Fin(n+2).
- Исполнимый nearest-node k=floor((x+1)(n+1)/2).
- Scalar coverage radius 2/(n+1).
- Pair coverage в max-метрике для (t,v).
- Serializable RationalParameterNode с hemisphere bit.
- Доказанный предел delta_n->0.

## Статус утверждения

Refinement является конечным, рациональным, исполнимым и сходящимся в parameter space. Diamond lift ещё не заявлен.

## Проверяемый носитель

- `formal/IntrinsicNonradialShearRationalParameterRefinement.lean`
- `formal/IntrinsicNonradialShearRationalParameterRefinementAudit.lean`

## Красная граница

Нужны stereographic surjectivity и quantitative Lipschitz transport в BlowUpPoint.

## Следующий шаг

IF-BS-22F-F8C31B: stereographic diamond lift.
