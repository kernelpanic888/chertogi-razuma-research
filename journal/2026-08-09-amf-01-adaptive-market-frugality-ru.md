# AMF-01 / Адаптивная бережливость рынка

**Дата:** 2026-08-09  
**Статус:** авторская модель, проверенная Lean · живой публичный ридер  
**Автор:** Салкуцан Алексей Анатольевич  
**ORCID:** 0009-0006-8717-0492

## Результат

Адаптивная бережливость формализована как политика запаса, ограниченного назначением, а не как бесконечное накопление.

Состояние:

\[
s_t=(K_t,R_t,C_t,\varepsilon_t,A_t,\rho_t,H_t)
\]

Дискретный ресурсный переход:

\[
K_{t+1}=K_t+R_t-C^{eff}_t-I_A(a_t)-\varepsilon_t
\]

Целевой буфер авторской модели и полоса неопределённости:

\[
K_t^*=\frac{(\rho_t+1)(H_t+1)}{A_t+1},
\qquad
\delta_t=\varepsilon_t+1
\]

Риск и длинный неблагоприятный горизонт повышают цель. Адаптивность уменьшает потребность в пассивном запасе.

## Селектор

Переиспользован существующий проверяемый Selector.

- K + δ < K* выбирает accumulate.
- При отсутствии обоих строгих неравенств выбирается hold.
- K* + δ < K выбирает адаптацию, снижение риска либо расходы на качество.
- Если предпочтительного действия нет в открытом поле действий, селектор возвращает none.

GreedAt означает продолжение накопления выше буферной полосы. AdaptiveFrugalityAt направляет избыток в устойчивость либо живую функцию системы.

## Проверенная поверхность

Новый модуль компилируется в Lean 4 и доказывает:

- selector_below_buffer
- selector_near_buffer
- selector_above_buffer
- selector_above_buffer_not_accumulate
- preferredAction_is_adaptively_frugal
- preferredAction_is_not_greedy_at
- selected_transition_is_admitted

## Интерфейсы

- [Живой ридер](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/adaptive-market-frugality/)
- [Lean-исходник](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AdaptiveMarketFrugality.lean)
- [Исходник ридера](https://github.com/kernelpanic888/chertogi-razuma-research/blob/main/public/readers/adaptive-market-frugality/index.html)
- [Интерфейс корпуса](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/corpus-interface/)

## Внешние опоры

- [ISO 31000:2018](https://www.iso.org/standard/65694.html)
- [Federal Reserve Banks, 2025 Report on Employer Firms](https://www.fedsmallbusiness.org/-/media/project/clevelandfedtenant/fsbsite/reports/2025/2025-report-on-employer-firms.pdf)
- [OECD, Financing SMEs and Entrepreneurs 2026](https://www.oecd.org/en/publications/financing-smes-and-entrepreneurs-2026_075d8058-en.html)
- [Teece, Pisano and Shuen, Dynamic Capabilities and Strategic Management](https://sms.onlinelibrary.wiley.com/doi/10.1002/%28SICI%291097-0266%28199708%2918%3A7%3C509%3A%3AAID-SMJ882%3E3.0.CO%3B2-Z)
- [Toyota Production System](https://global.toyota/en/company/vision-and-philosophy/production-system/)

## Красная граница

Lean проверяет следствия объявленной дискретной политики. Он не устанавливает эмпирическую калибровку, рыночную оптимальность, максимизацию прибыли или финансовую пригодность. Единичные стоимости и точная формула целевого буфера являются явным выбором авторской модели.

## Следующий шов

AMF-02 должен зафиксировать паспорт калибровки и корпус неблагоприятных сценариев до допуска любых практических рекомендаций.
