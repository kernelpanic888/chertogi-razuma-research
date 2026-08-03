# IF-BS-22F-F8B2 / Summable compact tent witness

## Русское чтение

F8B1 дал один локальный homeomorphism. F8B2 собирает из таких карт бесконечный маршрут с точным ненулевым пределом.

Амплитуды выбраны как

`a_n = (1/2)(1 - 2^(-n))`.

Они возрастают от нуля к `1/2`. Канонический `n`-й префикс равен

`H_(a_n)(x) = x + a_n max(0,1-|x|)`.

Между соседними префиксами вводится настоящий локальный шаг

`T_n = H_(a_(n+1)) o H_(a_n)^(-1)`.

Композиция телескопируется точно:

`T_(n-1) o ... o T_0 = H_(a_n)`.

Чтобы не накапливать грубые оценки, каждый переход получает собственные точные bounds

`L_n = (1+a_(n+1))/(1+a_n)`,

`M_n = (1-a_n)/(1-a_(n+1))`.

Их произведения сокращаются:

`prod_(k<n) L_k = 1+a_n <= 3/2`,

`prod_(k<n) M_k = 1/(1-a_n) <= 2`.

Прямые префиксы глобально и равномерно сходятся к `H_(1/2)`. Обратные префиксы также глобально и равномерно сходятся к `H_(1/2)^(-1)`. Поэтому F7 применим без ослабления: предел является homeomorphism, его интерфейс является actual frontier, а точные движущиеся интерфейсы и вычислимые носители сходятся к нему в стандартном Hausdorff distance.

Все карты, шаги и предел тождественны вне `[-1,1]`. В отличие от F8A, движение действительно локально.

## English reading

Set `a_n=(1/2)(1-2^(-n))` and let `H_(a_n)(x)=x+a_n max(0,1-|x|)`. Define the local step `T_n=H_(a_(n+1)) o H_(a_n)^(-1)`. Prefixes telescope exactly to `H_(a_n)`. The exact step constants are `L_n=(1+a_(n+1))/(1+a_n)` and `M_n=(1-a_n)/(1-a_(n+1))`; their products telescope to `1+a_n<=3/2` and `1/(1-a_n)<=2`. Both the direct and inverse prefixes converge uniformly on all of `Real` to `H_(1/2)` and its inverse. F7 therefore yields a genuine limit homeomorphism, an actual transported frontier, and Hausdorff convergence of exact and computed carriers. Every map is the identity outside `[-1,1]`.

## Red boundary

The infinite local witness is one-dimensional. The next geometric obligation is to lift the same telescoping control to a compactly supported deformation of a planar boundary chamber without losing actual-frontier semantics.
