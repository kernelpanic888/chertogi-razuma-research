# IF-BS-22F-F8C30 / Executable rational coarse net

## RU

### Задача

F8C29 доказал transport для любого сертифицированного finite sample. F8C30 предъявляет первый полностью явный sample, для которого coverage, принадлежность домену, измерение и формат записи проверяются машиной.

### Рациональный якорь

Берётся точка

c0=((1,0),0).

Её координаты рациональны, direction лежит на единичной окружности, slope равен нулю, поэтому c0 принадлежит exact directional diamond.

### Грубое покрытие

Для любой точки p diamond-камеры:

dist(direction(p),(1,0))<=2,

|slope(p)|<=sqrt(2)<=2.

Поскольку product metric является максимумом двух расстояний,

D subset Ball(c0,2).

Следовательно G0={c0} является явной delta0=2 сетью.

### Исполнимая запись

RationalMeasurementRecord хранит nodeId и три рациональных числа: measured, instrumentNoise, computationalResolution. Эталонная запись равна

{nodeId=0, measured=1, instrumentNoise=0, computationalResolution=0}.

Её Boolean checker вычисляется в true. На c0 forwardBlowUpSq=1 и inverseBlowUpSq=1 для любого amplitude, поэтому обе split-budget validity теоремы доказываются без внешнего oracle.

### Сквозной результат

Для каждого 0<=a<1 singleton sample проходит F8C29, порождает CertifiedNoisyMetricReading и входит в доказанный интервал F8C28.

Сертификат намеренно грубый: он доказывает существование полностью исполнимого канала, а не высокую точность.

### Красная граница

Нужна последовательность явных рациональных refinement-сетей с delta_n->0 и parser для внешних сериализованных records.

## EN

### Problem

F8C29 proved the transport for any certified finite sample. F8C30 supplies the first fully explicit sample whose coverage, domain membership, measurement and record shape are machine checked.

### Rational anchor

Take

c0=((1,0),0).

Its coordinates are rational, its direction lies on the unit circle and its slope is zero, hence c0 belongs to the exact directional diamond.

### Coarse coverage

For every point p in the diamond chamber,

dist(direction(p),(1,0))<=2,

|slope(p)|<=sqrt(2)<=2.

The product metric is the maximum of these distances, so

D subset Ball(c0,2).

Therefore G0={c0} is an explicit delta0=2 net.

### Executable record

RationalMeasurementRecord stores a nodeId and three rational numbers: measured, instrumentNoise and computationalResolution. The reference record is

{nodeId=0, measured=1, instrumentNoise=0, computationalResolution=0}.

Its Boolean checker evaluates to true. At c0 both forwardBlowUpSq and inverseBlowUpSq equal 1 for every amplitude, so both split-budget validity theorems require no external oracle.

### End-to-end result

For every 0<=a<1 the singleton sample passes F8C29, produces a CertifiedNoisyMetricReading and enters the proved F8C28 interval.

The certificate is intentionally coarse: it proves a fully executable channel, not high precision.

### Red boundary

We still need an explicit sequence of rational refinement nets with delta_n->0 and a parser for external serialized records.
