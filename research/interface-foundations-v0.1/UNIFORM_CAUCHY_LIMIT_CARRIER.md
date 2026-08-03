# IF-BS-22F-F6 / Uniform-Cauchy limit carrier

## Русское чтение

Пусть `F_n` является последовательностью накопленных controlled-преобразований, а `I` является исходным компактным интерфейсом. Если ограничения `F_n|I` равномерно Cauchy и окружающее метрическое пространство полно, то существует единое предельное отображение `F_infinity`, причём `F_n` сходится к нему равномерно на всём `I`.

Предельный носитель определяется формулой `I_infinity = F_infinity[I]`. Он непуст и компактен. Точные движущиеся интерфейсы `I_n = F_n[I]` сходятся к `I_infinity` в стандартном расстоянии Хаусдорфа:

`d_H(I_n, I_infinity) -> 0`.

Если одновременно выполнено условие F5 `P_n <= C`, где `P_n` является произведением прямых Lipschitz-констант, то вычислимые носители `K_n^(n)` сходятся к тому же общему носителю:

`d_H(K_n^(n), I_infinity) -> 0`.

Это впервые заменяет движущуюся цель одним общим пределом.

## English reading

Let `F_n` be the accumulated controlled transformations and let `I` be the compact source interface. If the restrictions `F_n|I` are uniformly Cauchy and the ambient metric space is complete, then there is one limit map `F_infinity`, with `F_n` converging uniformly to it on all of `I`.

Define the common carrier by `I_infinity = F_infinity[I]`. It is nonempty and compact. The exact moving interfaces `I_n = F_n[I]` converge to `I_infinity` in the standard Hausdorff metric. Under the F5 bounded-product condition, the moving computational carriers converge to that same set.

## Red boundary

The theorem proves a compact common carrier. It does not yet prove that `F_infinity` is a homeomorphism or that `I_infinity` is the frontier of a limiting inside region. That stronger conclusion needs compatible uniform control of the inverse prefix maps.
