# IF-BS-22F-F8C29 / Raw finite sample certification

## RU

### Задача

F8C28 принимал готовые бюджеты ошибок. F8C29 выводит их из конечной delta-сети, ограниченного приборного шума и вычислительного разрешения.

### Сырые данные

Для каждого измерения фиксируются точка, значение m_i и полный бюджет e_i=eta+rho, где eta ограничивает приборный шум, а rho — вычислительное округление. Валидность означает |m_i-f(p_i)|<=e_i.

### Квадратный сертификат

Для неотрицательного квадратичного observable с модулем регулярности L строятся

S_minus=max(0,max_i(m_i-e_i)),

S_plus=max_i(m_i+e_i)+L delta.

Если sample лежит в точном diamond, покрывает его с радиусом delta и exact maximum действительно является максимумом observable, то

S_minus <= S_exact <= S_plus.

### Перенос через корень

Наблюдаемое метрическое значение и его ошибка определяются без скрытого fit:

O=sqrt(S_plus),

epsilon=sqrt(S_plus)-sqrt(S_minus).

Монотонность корня даёт |O-sqrt(S_exact)|<=epsilon.

### Два канала

Forward channel использует forward regularity. Inverse channel использует sharp reciprocal regularity на всём диапазоне 0<=a<1. Вместе они автоматически образуют CertifiedNoisyMetricReading и входят в интервал F8C28.

### Красная граница

Coverage, sample-inside и split error validity пока являются проверяемыми условиями сертификата. Следующий шаг — явная рациональная delta-сеть и исполнимый interval-arithmetic checker, который вычисляет эти свидетельства из файла измерений.

## EN

### Problem

F8C28 consumed ready-made error budgets. F8C29 derives them from a finite delta-net, bounded instrument noise and computational resolution.

### Raw data

Each reading stores a point, a measured value m_i and a total budget e_i=eta+rho, where eta bounds instrument noise and rho bounds numerical rounding. Validity means |m_i-f(p_i)|<=e_i.

### Square certificate

For a nonnegative squared observable with regularity modulus L define

S_minus=max(0,max_i(m_i-e_i)),

S_plus=max_i(m_i+e_i)+L delta.

If the sample lies in the exact diamond, delta-covers it and the exact value is the true maximum of the observable, then

S_minus <= S_exact <= S_plus.

### Square-root transport

The observed metric value and its error are defined without a hidden fit:

O=sqrt(S_plus),

epsilon=sqrt(S_plus)-sqrt(S_minus).

Monotonicity of the square root gives |O-sqrt(S_exact)|<=epsilon.

### Two channels

The forward channel uses forward regularity. The inverse channel uses sharp reciprocal regularity on the full range 0<=a<1. Together they automatically form a CertifiedNoisyMetricReading and enter the F8C28 interval.

### Red boundary

Coverage, sample-inside and split-error validity remain checkable certificate conditions. The next step is an explicit rational delta-net and an executable interval-arithmetic checker deriving these witnesses from a measurement file.
