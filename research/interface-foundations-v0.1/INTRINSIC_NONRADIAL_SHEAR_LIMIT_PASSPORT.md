# Паспорт IF-BS-22F-F8C4

## Точка маршрута

`IF-BS-22F-F8C4 / INTRINSIC SHEAR -> NEAR-IDENTITY CONTROL -> ACTUAL FRONTIER`

## Вход

- Одномерный compact tent-homeomorphism из F8B1.
- Controlled transport и common-limit machinery из F1-F7.
- Full-plane nonradial stress test F8C3.

## Выход

- Построена intrinsic карта `S_a(x,y)=(x,y+a phi(x)phi(y))`.
- Биективность доказана fiberwise без линейного сопряжения.
- Доказана непрерывность прямой и обратной карты.
- Получен full-plane homeomorphism.
- Доказаны forward bound `1+2a` и co-Lipschitz bound `1-2a`.
- Построен two-sided ControlledEquiv с общей константой `1+4a`.
- Константа стремится к `1` при `a->0`.
- Карта и inverse тождественны вне compact carrier `closedBall(0,2)`.
- Нерадиальность доказана equal-norm witness без смены координат.
- Каноническая family имеет единый bound `2`.
- Direct и inverse families глобально равномерно сходятся.
- Предельный интерфейс является actual frontier.
- Точные и вычислимые носители сходятся к пределу в Hausdorff distance.

## Проверяемая формула

`S_a(x,y)=(x,y+a phi(x)phi(y))`

`(1-2a)d(p,q) <= d(S_a(p),S_a(q)) <= (1+2a)d(p,q)`

`Lip(S_a), Lip(S_a^(-1)) <= 1+4a`, `0<=a<=1/4`.

`a_n=(1/4)(1-2^(-n))`, `S_(a_n) -> S_(1/4)` uniformly.

## Красная граница

`closedBall(0,2)` является доказанным compact carrier, но не минимальным support. Оптимальная константа и точная square-like геометрия множества движения пока не выделены.

## Русская вычитка

Нерадиальность больше не вносится внешней системой координат. Направление деформации записано внутри самого закона, но исчезает вместе с амплитудой. Поэтому при нулевом шаге карта и её контроль возвращаются к тождеству, а при бесконечном числе согласованных состояний actual frontier сохраняется.

## Следующий шаг по паспорту

`IF-BS-22F-F8C5`: выделить точное минимальное support closure intrinsic shear, доказать его square-like frontier и исследовать sharp constants вместо безопасного bound `1+4a`.
