# IF-BS-22F-F8C27 / Least direct and inverse metric constants

## RU

### Задача

F8C26 доказал минимальность модуля изменения `Phi_a` на blow-up diamond. Это не та же оптимизация, что максимум самого отношения расстояний: метрическую константу нельзя получить как `sqrt(L_tan)`. F8C27 соединяет точные diamond-полюса с ранее построенной spectral-геометрией исходного нелинейного сдвига.

### Два квадратных полюса

Пусть

`lambda_+(a)=1+a+a^2+a sqrt((1+a)^2+1)`,

`lambda_-(a)=1-a+a^2-a sqrt((1-a)^2+1)`.

F8C17 доказал, что это точные максимум и минимум `Phi_a` на полном directional diamond. В F8C27 формально установлены тождества

`lambda_+(a)=forwardSpectralSq(a)`,

`lambda_-(a) inverseSpectralSq(a)=1` для `0<=a<1`.

### Метрические константы

Определим

`K_+(a)=sqrt(lambda_+(a))`,

`K_-(a)=1/sqrt(lambda_-(a))`.

Первая константа ограничивает прямую карту, вторая — восстановление входного расстояния по выходному:

`d(S_a p,S_a q)<=K_+(a)d(p,q)`,

`d(p,q)<=K_-(a)d(S_a p,S_a q)`.

### Минимальность

Вводятся множества всех неотрицательных констант, удовлетворяющих каждому из двух неравенств на всей плоскости. Ранее построенные конечные spectral-пробы исключают каждую меньшую константу. Поэтому

`IsLeast(ForwardNonnegativeMetricModuli(a),K_+(a))`,

`IsLeast(BackwardNonnegativeMetricModuli(a),K_-(a))`.

При `0<=a<1` оба утверждения доказаны одновременно.

### Красная граница

Глобальные sharp constants известны как функции параметра `a`. Следующая задача — конечная идентификация `a` по наблюдаемым и зашумлённым отношениям расстояний с честным интервалом неопределённости.

## EN

### Problem

F8C26 proved leastness of the variation modulus of `Phi_a` on the blow-up diamond. This is not the same optimization as maximizing the distance ratio itself: the metric constant is not `sqrt(L_tan)`. F8C27 connects the exact diamond poles to the existing spectral geometry of the original nonlinear shear.

### Two squared poles

Let

`lambda_+(a)=1+a+a^2+a sqrt((1+a)^2+1)`,

`lambda_-(a)=1-a+a^2-a sqrt((1-a)^2+1)`.

F8C17 proved that these are the exact maximum and minimum of `Phi_a` on the full directional diamond. F8C27 establishes

`lambda_+(a)=forwardSpectralSq(a)`,

`lambda_-(a) inverseSpectralSq(a)=1` for `0<=a<1`.

### Metric constants

Define

`K_+(a)=sqrt(lambda_+(a))`,

`K_-(a)=1/sqrt(lambda_-(a))`.

The first bounds the forward map and the second reconstructs input distance from output distance:

`d(S_a p,S_a q)<=K_+(a)d(p,q)`,

`d(p,q)<=K_-(a)d(S_a p,S_a q)`.

### Leastness

Consider all nonnegative constants satisfying each inequality globally. Existing finite spectral probes defeat every smaller constant. Hence

`IsLeast(ForwardNonnegativeMetricModuli(a),K_+(a))`,

`IsLeast(BackwardNonnegativeMetricModuli(a),K_-(a))`.

For `0<=a<1`, both statements hold simultaneously.

### Red boundary

The global sharp constants are known as functions of `a`. The next problem is finite identification of `a` from observed noisy distance ratios with an honest uncertainty interval.
