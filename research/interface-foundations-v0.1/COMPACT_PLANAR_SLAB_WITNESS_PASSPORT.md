# Паспорт IF-BS-22F-F8C1

## Точка маршрута

`IF-BS-22F-F8C1 / 1D LOCAL LIMIT -> COMPACT PLANAR SUPPORT CARRIER`

## Вход

- `PlanarSlab = Real x [-1,1]`.
- Телескопическая последовательность `T_n` из F8B2.
- Одномерный предел `H_(1/2)`.
- Product metric и F7.

## Выход

- Построен product homeomorphism `(x,y) -> (H(x),y)`.
- Controlled lift сохраняет исходные forward/inverse constants, если они не меньше единицы.
- Planar step sequence имеет те же step constants, что и F8B2.
- Префиксы точно равны `(F_n(x),y)`.
- Префиксные bounds остаются `3/2` и `2`.
- Прямые и обратные planar-префиксы глобально равномерно сходятся.
- `K=[-1,1]x[-1,1]` является компактным support carrier.
- Каждый step, prefix и limit тождественен вне `K`.
- Для любой `ComputableBoundaryModel PlanarSlab` предел является actual frontier.
- Точные интерфейсы и вычислимые носители сходятся к пределу в Hausdorff distance.

## Проверяемая формула

`P_n(x,y)=(H_(a_n)(x),y)`

`(x,y) notin K -> P_n(x,y)=(x,y)`

`P_n -> P_infinity=(H_(1/2),id)`.

## Красная граница

Компактная поддержка доказана на planar slab. Продолжение этой карты как homeomorphism всего `AmbientPlane` пока не построено.

## Русская вычитка

Одномерное локальное движение стало двумерной камерой без размывания поддержки. Вторая координата не является декоративной: она ограничивает поперечный размер физической зоны, превращая отрезок поддержки в компактный квадрат. Снаружи квадрата пространство остаётся буквально неподвижным.

## Следующий шаг по паспорту

`IF-BS-22F-F8C2`: построить явное compactly supported продолжение в существующий `AmbientPlane`, доказать homeomorphism и two-sided bounds, затем перенести на него actual-frontier limit F8C1.
