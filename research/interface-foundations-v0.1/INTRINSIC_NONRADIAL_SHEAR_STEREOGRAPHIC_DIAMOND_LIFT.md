# IF-BS-22F-F8C31B / Two-chart stereographic diamond lift

## EN / Reading

The parameter grid from F8C31A lives in two copies of the square [-1,1]^2. F8C31B gives those squares an exact geometric meaning.

For t in [-1,1], define X(t) = (1-t^2)/(1+t^2) and Y(t) = 2t/(1+t^2).

The east chart uses (X(t),Y(t)); the west chart uses (-X(t),Y(t)). Together they cover the unit circle. For a direction d=(x,y), let w(d)=|x|+|y|. The second parameter v in [-1,1] produces the admissible slope s=v w(d).

The direct theorem proves that every (hemisphere,t,v) lands in the exact directional diamond. The inverse theorem proves that every point of the diamond has such parameters:

- east: t=y/(1+x) when x>=0;
- west: t=y/(1-x) when x<=0;
- fiber: v=s/(|x|+|y|).

The width is strictly positive on the unit circle, so the inverse fiber coordinate is always defined.

## RU / Чтение

Параметрическая сетка F8C31A живёт в двух копиях квадрата [-1,1]^2. F8C31B придаёт этим квадратам точный геометрический смысл.

Для t in [-1,1] задаются X(t) = (1-t^2)/(1+t^2) и Y(t) = 2t/(1+t^2).

Восточная карта использует (X(t),Y(t)), западная — (-X(t),Y(t)). Вместе они покрывают единичную окружность. Для направления d=(x,y) вводится ширина w(d)=|x|+|y|. Второй параметр v in [-1,1] задаёт допустимый наклон s=v w(d).

Прямая теорема доказывает, что каждый набор (hemisphere,t,v) попадает в точный directional diamond. Обратная теорема доказывает, что каждая точка diamond имеет такие параметры:

- восток: t=y/(1+x) при x>=0;
- запад: t=y/(1-x) при x<=0;
- слой: v=s/(|x|+|y|).

На единичной окружности ширина строго положительна, поэтому обратная координата слоя всегда определена.

## Red boundary / Красная граница

Surjectivity is now closed. The remaining step is quantitative: prove a Lipschitz estimate for the lift on each compact chart and transport the grid radius 2/(n+1) into the ambient metric of BlowUpPoint.
