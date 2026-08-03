# IF-BS-22F-F8C31D: Rational measurement table

## Status

Working formal slice. The table is a mathematical, exactly generated dataset; it is not an external laboratory measurement.

## Row schema

Every row stores:

- a stable node identifier;
- hemisphere and finite grid indices;
- rational `t` and `v`;
- rational direction coordinates `x` and `y`;
- rational slope `s`;
- exact rational forward and inverse values;
- separate instrument-noise and computational-resolution fields.

Generated rows use zero in both error fields. An executable acceptance predicate verifies every redundant field against the node and amplitude.

## Materialization

At level `n`, every element of `RationalParameterNode n` is enumerated once into a finite list. The forward and inverse decoders produce the `NoisyUpperReading` lists required by F8C29.

## Certified chain

`rational row -> decoded exact point -> DeltaCoverage(20/(n+1)) -> F8C29 raw certificate -> F8C28 amplitude interval`.

## Honest boundary

These are exact computed records of the model. External instrument acquisition, nonzero empirical noise and a signed exchange format remain open.

---

# IF-BS-22F-F8C31D: Рациональная таблица измерений

## Статус

Рабочий формальный срез. Таблица является точно сгенерированным математическим набором данных, а не внешним лабораторным измерением.

## Схема строки

Каждая строка хранит:

- стабильный идентификатор узла;
- полусферу и конечные индексы сетки;
- рациональные `t` и `v`;
- рациональные координаты направления `x` и `y`;
- рациональный наклон `s`;
- точные рациональные прямое и обратное значения;
- отдельные поля инструментального шума и вычислительного разрешения.

У сгенерированных строк оба поля ошибки равны нулю. Исполняемый предикат приёмки сверяет каждое избыточное поле с узлом и амплитудой.

## Материализация

На уровне `n` каждый элемент `RationalParameterNode n` один раз перечисляется в конечный список. Прямой и обратный декодеры создают списки `NoisyUpperReading`, требуемые F8C29.

## Сертифицированная цепочка

`рациональная строка -> декодированная точная точка -> DeltaCoverage(20/(n+1)) -> сырой сертификат F8C29 -> интервал амплитуды F8C28`.

## Честная граница

Это точные вычисленные записи модели. Получение данных от внешнего прибора, ненулевой эмпирический шум и подписанный формат обмена остаются открытыми.
