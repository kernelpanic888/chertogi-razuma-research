# IF-BS-22F-F7 / Two-sided limit homeomorphism

## Русское чтение

Пусть `F_n` является последовательностью накопленных controlled-преобразований всего пространства, а `G_n = F_n^{-1}`. Предположим, что обе последовательности равномерно Cauchy на всём пространстве и что их прямые и обратные Lipschitz-константы имеют единые конечные границы.

Полнота пространства даёт равномерные пределы `F_infinity` и `G_infinity`. Единые Lipschitz bounds позволяют перенести точные тождества `G_n(F_n(x)) = x` и `F_n(G_n(x)) = x` через предел:

`G_infinity(F_infinity(x)) = x`,

`F_infinity(G_infinity(x)) = x`.

Следовательно, `F_infinity` является homeomorphism, а `G_infinity` является его непрерывным обратным отображением. Для исходной области `A` и интерфейса `I = frontier(A)` получаем:

`frontier(F_infinity[A]) = F_infinity[I]`.

И точные префиксные интерфейсы, и вычислимые носители сходятся в стандартной Hausdorff-метрике к этому actual frontier.

## English reading

Let `F_n` be the accumulated controlled transformations of the whole space and let `G_n = F_n^{-1}`. Assume that both sequences are uniformly Cauchy globally and that their forward and inverse Lipschitz constants admit uniform finite bounds.

Completeness supplies uniform limits `F_infinity` and `G_infinity`. The uniform Lipschitz bounds pass the exact identities of every finite prefix through the limit. Thus the two limits are mutually inverse continuous maps, so `F_infinity` is a homeomorphism. The common F6 carrier is therefore the actual frontier of the transported limit region.

## Red boundary

Global uniform-Cauchy convergence on an unbounded ambient space is a strong hypothesis. F7 proves the transfer theorem; it does not yet construct a nontrivial infinite controlled sequence satisfying all hypotheses.
