# IF-BS-22F-F8A / Summable translation witness

## Русское чтение

F7 является общей теоремой переноса. F8A предъявляет первую явную бесконечную последовательность, удовлетворяющую всем её аналитическим условиям.

Зададим целевой префиксный сдвиг

`s_n = 1 - 2^(-n)`

и шаг

`delta_n = s_(n+1) - s_n`.

Каждый controlled-шаг является переносом `T_n(x) = x + delta_n`. Телескопический закон даёт точную форму накопленного префикса:

`F_n(x) = x + s_n`.

Поскольку `s_n -> 1`, получаем глобальную равномерную сходимость

`F_n(x) -> x + 1`,

`F_n^(-1)(x) -> x - 1`.

Каждый шаг и каждый префикс являются изометриями, поэтому прямые и обратные Lipschitz-константы точно равны единице. F7 применяется без потери и даёт предельный homeomorphism `H_infinity(x)=x+1`. Для любой ранее построенной вычислимой модели её точные интерфейсы и вычислимые носители сходятся к actual frontier перенесённой на единицу области.

## English reading

Set `s_n = 1 - 2^(-n)` and `delta_n = s_(n+1)-s_n`. Let the `n`-th controlled step be translation by `delta_n`. The prefix telescopes exactly to `F_n(x)=x+s_n`. Hence the forward prefixes converge uniformly on all of `Real` to `x+1`, while the inverse prefixes converge uniformly to `x-1`. Every step and prefix is an isometry, so both Lipschitz bounds are exactly `1`. This is a nontrivial explicit witness for F7.

## Red boundary

The witness is global: translations are not locally or compactly supported on `Real`. F8B must replace this calibration family by a genuinely local compactly supported deformation while retaining summable motion and two-sided bounds.
