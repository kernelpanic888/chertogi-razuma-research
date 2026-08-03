# Паспорт IF-BS-22F-F8C26

## Имя

Finite saturation and least global modulus / Конечное насыщение и наименьший глобальный модуль.

## Вход

- Точная касательная точка и модуль F8C21–F8C22.
- Точная центрированная огибающая F8C24.
- Глобальная верхняя оценка на всех реальных парах F8C25.

## Новые доказанные узлы

- Явная положительная шкала `k_n=1/(n+4)` и радиус `r_n=sqrt(1-k_n^2)`.
- Две допустимые конечные точки directional diamond для каждого `n`.
- Точное расстояние пары `d(p_n,q_n)=2k_n`.
- Точная факторизация конечной разности через `A_n 2k_n`.
- Сходимость `A_n -> L_tan(a)`.
- Нижняя оценка `L_tan(a)<=C` для любого глобального модуля `C`.
- Итоговый `IsLeast(GlobalDiamondChordModuli(a), L_tan(a))`.

## Статус утверждения

`L_tan(a)` является точным наименьшим глобальным модулем squared blow-up observable на полном directional diamond при `a>=0`.

## Проверяемый носитель

- `formal/IntrinsicNonradialShearFiniteSaturation.lean`
- `formal/IntrinsicNonradialShearFiniteSaturationAudit.lean`

## Красная граница

Результат относится к квадрату растяжения в blow-up камере. Точные sharp direct/inverse constants исходной метрики и единый оптимальный bilipschitz envelope ещё не получены.

## Следующий шаг

IF-BS-22F-F8C27: перенести least squared modulus в sharp direct metric distortion и исследовать обратную минимальность.
