# IF-BS-22F-F8C31E: Canonical interchange and replay

## Format

`IFBS31E/1` is a newline-delimited, dependency-free interchange format. Every rational value is written uniquely as a reduced integer numerator and a positive natural denominator.

Header:

`IFBS31E|1|level|amplitude|row-count`

Row:

`ROW|level|node-id|hemisphere|t-index|v-index|t|v|x|y|s|forward|inverse|instrument-noise|resolution`

Rows are sorted by `node-id`. The complete range must occur exactly once.

## Replay rule

The verifier does not trust derived fields. From `level`, hemisphere and the two indices it reconstructs `t` and `v`, then recomputes `x`, `y`, width, slope, forward value and inverse value using exact rational arithmetic. Any nonreduced fraction, duplicate, missing row or changed field is rejected.

## Dual implementation

- Lean proves rational encode/decode round-trip, generated-row acceptance, complete-envelope replay soundness and deterministic row count.
- The standalone Node verifier uses only `BigInt`, reads the stored fixture and recomputes every field independently of Lean and the website.

## Boundary

This proves deterministic interchange for exact model records. Cryptographic authorship, external acquisition and empirical error calibration remain separate tasks.

---

# IF-BS-22F-F8C31E: Канонический обмен и воспроизведение

## Формат

`IFBS31E/1` — построчный формат обмена без зависимостей. Каждое рациональное число записывается однозначно как сокращённый целый числитель и положительный натуральный знаменатель.

Заголовок:

`IFBS31E|1|уровень|амплитуда|число-строк`

Строка:

`ROW|уровень|node-id|полусфера|t-index|v-index|t|v|x|y|s|forward|inverse|instrument-noise|resolution`

Строки отсортированы по `node-id`. Полный диапазон должен встретиться ровно один раз.

## Правило воспроизведения

Проверяющий модуль не доверяет производным полям. Из уровня, полусферы и двух индексов он восстанавливает `t` и `v`, затем заново вычисляет `x`, `y`, ширину, наклон, прямое и обратное значения в точной рациональной арифметике. Несокращённая дробь, дубликат, пропущенная строка или изменённое поле отклоняются.

## Двойная реализация

- Lean доказывает round-trip рационального кодирования, приёмку сгенерированной строки, корректность полного replay и детерминированное число строк.
- Самостоятельный Node-проверяющий модуль использует только `BigInt`, читает сохранённый fixture и пересчитывает каждое поле независимо от Lean и сайта.

## Граница

Здесь доказан детерминированный обмен точными записями модели. Криптографическое авторство, внешнее получение данных и калибровка эмпирической ошибки остаются отдельными задачами.
