# IF-BS-22F-F8C31A / Rational parameter refinement

## RU

### Задача

F8C30 дал первый исполнимый singleton с радиусом 2. F8C31A строит конечную рациональную refinement-сеть в параметрической камере (hemisphere,t,v), где t и v лежат в [-1,1].

### Явная сетка

На уровне n используется denominator N=n+1 и узлы

q_k=-1+2k/N, 0<=k<=N.

Каждый q_k является рациональным числом и одновременно имеет точный вещественный decode.

### Исполнимый nearest-node

Для x in [-1,1] вычисляется

k=floor((x+1)N/2).

Формально доказано k<=N и

|x-q_k|<=2/N.

Никакой compactness oracle здесь не используется.

### Двумерный параметрический узел

RationalParameterNode хранит hemisphere:Bool и два конечных индекса tIndex,vIndex. Для любой пары (t,v) in [-1,1]^2 существует узел того же hemisphere с

max(|t-t_k|,|v-v_j|)<=delta_n,

delta_n=2/(n+1).

### Предел

Lean доказывает delta_n->0 и eventually delta_n<epsilon для каждого epsilon>0.

### Красная граница

Сетка пока живёт в параметрической камере. F8C31B должен доказать, что stereographic decode покрывает весь exact diamond и переносит parameter radius в явный BlowUpPoint radius.

## EN

### Problem

F8C30 supplied the first executable singleton with radius 2. F8C31A constructs a finite rational refinement grid in the parameter chamber (hemisphere,t,v), where t and v lie in [-1,1].

### Explicit grid

At level n let N=n+1 and define

q_k=-1+2k/N, 0<=k<=N.

Every q_k is rational and has an exact real decode.

### Executable nearest node

For x in [-1,1] compute

k=floor((x+1)N/2).

The formal proof establishes k<=N and

|x-q_k|<=2/N.

No compactness oracle is used.

### Two-dimensional parameter node

RationalParameterNode stores hemisphere:Bool and two finite indices tIndex,vIndex. For every pair (t,v) in [-1,1]^2 there is a node in the same hemisphere satisfying

max(|t-t_k|,|v-v_j|)<=delta_n,

delta_n=2/(n+1).

### Limit

Lean proves delta_n->0 and eventually delta_n<epsilon for every epsilon>0.

### Red boundary

The grid still lives in parameter space. F8C31B must prove that stereographic decoding covers the entire exact diamond and transports the parameter radius into an explicit BlowUpPoint radius.
