# IF-BS-22F-F8C28 / Certified noisy identifiability

## RU

### Задача

F8C27 даёт точные sharp constants `K_+(a)` и `K_-(a)` при известном параметре `a`. F8C28 рассматривает обратную задачу: какой интервал для `a` гарантируется наблюдаемыми значениями с известной погрешностью?

### Сертифицированное чтение

Наблюдение `(F,B,eps_F,eps_B)` сертифицирует параметр `a`, если

`0<=a<1`, `eps_F,eps_B>=0`,

`|F-K_+(a)|<=eps_F`,

`|B-K_-(a)|<=eps_B`.

Это условие не утверждает, что произвольный конечный sample уже измерил глобальный полюс. Погрешность должна включать и шум прибора, и ещё не построенную mesh-поправку.

### Явный внешний интервал

Используются четыре проверенные связи:

`F-eps_F <= K_+(a) <= F+eps_F`,

`1+a <= K_+(a) <= 1+sqrt(2)a`,

`K_-(a) <= B+eps_B`,

`1/(1-a) <= K_-(a)`.

Отсюда

`a_low=max(0,(F-eps_F-1)/sqrt(2))`,

`a_high=min(F+eps_F-1,(B+eps_B-1)/(B+eps_B))`,

и каждый совместимый параметр удовлетворяет

`a in [a_low,a_high]`.

### Непустота и точная идентифицируемость

Если чтение сертифицирует настоящий параметр, feasible set непуст. Если обе ошибки равны нулю, строгая монотонность `K_+` даёт единственность:

`Compatible(a_1,F,B,0,0) and Compatible(a_2,F,B,0,0) => a_1=a_2`.

Явный интервал является доказанным внешним сертификатом и может быть шире точного feasible set.

### Красная граница

Пока погрешности являются входом модели. Следующий шаг должен вывести `eps_F` и `eps_B` из конечной delta-сети, разрешения вычисления и ограниченного измерительного шума.

## EN

### Problem

F8C27 gives the exact sharp constants `K_+(a)` and `K_-(a)` when `a` is known. F8C28 asks the inverse question: which interval for `a` is guaranteed by noisy observed values with known error budgets?

### Certified reading

A reading `(F,B,eps_F,eps_B)` certifies `a` when

`0<=a<1`, `eps_F,eps_B>=0`,

`|F-K_+(a)|<=eps_F`,

`|B-K_-(a)|<=eps_B`.

This does not claim that an arbitrary finite sample measured the global poles. The error budget must cover both instrument noise and the still-missing mesh correction.

### Explicit outer interval

The proof uses four verified relations:

`F-eps_F <= K_+(a) <= F+eps_F`,

`1+a <= K_+(a) <= 1+sqrt(2)a`,

`K_-(a) <= B+eps_B`,

`1/(1-a) <= K_-(a)`.

Therefore

`a_low=max(0,(F-eps_F-1)/sqrt(2))`,

`a_high=min(F+eps_F-1,(B+eps_B-1)/(B+eps_B))`,

and every compatible parameter satisfies

`a in [a_low,a_high]`.

### Nonemptiness and exact identifiability

If the reading certifies a true parameter, the feasible set is nonempty. If both errors vanish, strict monotonicity of `K_+` gives uniqueness:

`Compatible(a_1,F,B,0,0) and Compatible(a_2,F,B,0,0) => a_1=a_2`.

The explicit interval is a proved outer certificate and may be wider than the exact feasible set.

### Red boundary

The error budgets are still inputs. The next step must derive `eps_F` and `eps_B` from a finite delta-net, computational resolution, and bounded measurement noise.
