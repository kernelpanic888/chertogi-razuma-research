# Паспорт IF-BS-22F-F8C28

## Имя

Certified noisy identifiability / Сертифицированная шумовая идентифицируемость.

## Вход

- Одновременно минимальные `K_+(a)` и `K_-(a)` из F8C27.
- Строгая монотонность forward spectral constant.
- Проверенные осевые и sqrt-two envelopes.

## Новые доказанные узлы

- Формальная модель сертифицированного noisy reading.
- Feasible set всех совместимых параметров `a`.
- Вычислимые `a_low` и `a_high`.
- Включение полного feasible set в `[a_low,a_high]`.
- Непустота feasible set при наличии истинного сертифицированного параметра.
- Единственность совместимого параметра при нулевой погрешности.

## Статус утверждения

Модель робастно ограничивает параметр при сертифицированных error budgets. Она ещё не выводит эти budgets из сырой конечной выборки.

## Проверяемый носитель

- `formal/IntrinsicNonradialShearNoisyIdentifiability.lean`
- `formal/IntrinsicNonradialShearNoisyIdentifiabilityAudit.lean`

## Красная граница

Нужен формальный мост `finite sample + mesh + bounded noise -> certified reading`.

## Следующий шаг

IF-BS-22F-F8C29: finite sample error-budget transport.
