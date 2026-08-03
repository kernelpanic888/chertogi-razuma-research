# IF-BS-22F-F8C2A / Compact radial twist homeomorphism

## Русское чтение

F8C1 работал на двумерном slab. F8C2A устраняет эту оговорку и строит homeomorphism уже на существующей полной евклидовой плоскости `AmbientPlane`.

Для угла `theta` определено обычное вращение

`R_theta(x,y) = (cos(theta)x - sin(theta)y, sin(theta)x + cos(theta)y)`.

В Lean доказаны два структурных закона:

`norm(R_theta(p)) = norm(p)`,

`R_alpha(R_beta(p)) = R_(alpha+beta)(p)`.

Локальный угол задаётся радиальным tent-профилем

`Theta_a(p) = a max(0,1-norm(p))`.

Radial twist имеет форму

`W_a(p) = R_(Theta_a(p))(p)`.

Поскольку вращение сохраняет норму, обратная карта получается без решения нелинейного уравнения:

`W_a^(-1) = W_(-a)`.

Прямая и обратная карты доказательно непрерывны, поэтому `W_a` является homeomorphism всего `AmbientPlane`.

Support carrier равен замкнутому единичному диску

`D = closedBall(0,1)`.

Диск компактен. Для `p` вне `D` tent-профиль равен нулю, поэтому одновременно

`W_a(p)=p`,

`W_a^(-1)(p)=p`.

## English reading

Define the Euclidean rotation `R_theta` and the radial angle `Theta_a(p)=a max(0,1-norm(p))`. The compact radial twist is `W_a(p)=R_(Theta_a(p))(p)`. Lean verifies norm preservation and angle addition for rotations. Hence the twist preserves radius and has the exact inverse `W_(-a)`. Both directions are continuous, so `W_a` is a homeomorphism of the full existing `AmbientPlane`. It is exactly the identity outside the compact closed unit disk.

## Red boundary

F8C2A proves topology, inverse, and compact support. It does not yet assign a verified global Lipschitz constant to `W_a`, so it is not yet a `ControlledEquiv` and the infinite F7 limit has not yet been transferred to the full plane.
