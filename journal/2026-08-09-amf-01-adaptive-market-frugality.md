# AMF-01 / Adaptive Market Frugality

**Date:** 2026-08-09  
**Status:** Lean-checked author model · live public reader  
**Author:** Salkutsan Aleksey Anatolievich  
**ORCID:** 0009-0006-8717-0492

## Result

Adaptive frugality is formalized as a bounded-purpose reserve policy rather than indefinite accumulation.

The state is:

\[
s_t=(K_t,R_t,C_t,\varepsilon_t,A_t,\rho_t,H_t)
\]

The discrete resource transition is:

\[
K_{t+1}=K_t+R_t-C^{eff}_t-I_A(a_t)-\varepsilon_t
\]

The author-model target buffer and uncertainty band are:

\[
K_t^*=\frac{(\rho_t+1)(H_t+1)}{A_t+1},
\qquad
\delta_t=\varepsilon_t+1
\]

Risk and a longer adverse horizon raise the target. Adaptability lowers the passive reserve requirement.

## Selector

The existing proof-carrying Selector is reused.

- K + δ < K* selects accumulate.
- Neither strict inequality selects hold.
- K* + δ < K selects adaptation, risk reduction or quality spending.
- If the preferred action is absent from the exposed action field, selection returns none.

GreedAt is the above-buffer choice to continue accumulation. AdaptiveFrugalityAt routes above-buffer surplus to resilience or the live function instead.

## Verified surface

The new module compiles in Lean 4 and proves:

- selector_below_buffer
- selector_near_buffer
- selector_above_buffer
- selector_above_buffer_not_accumulate
- preferredAction_is_adaptively_frugal
- preferredAction_is_not_greedy_at
- selected_transition_is_admitted

## Interfaces

- [Live reader](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/adaptive-market-frugality/)
- [Lean source](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AdaptiveMarketFrugality.lean)
- [Reader source](https://github.com/kernelpanic888/chertogi-razuma-research/blob/main/public/readers/adaptive-market-frugality/index.html)
- [Corpus interface](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/corpus-interface/)

## External shoulders

- [ISO 31000:2018](https://www.iso.org/standard/65694.html)
- [Federal Reserve Banks, 2025 Report on Employer Firms](https://www.fedsmallbusiness.org/-/media/project/clevelandfedtenant/fsbsite/reports/2025/2025-report-on-employer-firms.pdf)
- [OECD, Financing SMEs and Entrepreneurs 2026](https://www.oecd.org/en/publications/financing-smes-and-entrepreneurs-2026_075d8058-en.html)
- [Teece, Pisano and Shuen, Dynamic Capabilities and Strategic Management](https://sms.onlinelibrary.wiley.com/doi/10.1002/%28SICI%291097-0266%28199708%2918%3A7%3C509%3A%3AAID-SMJ882%3E3.0.CO%3B2-Z)
- [Toyota Production System](https://global.toyota/en/company/vision-and-philosophy/production-system/)

## Red boundary

Lean verifies consequences of the declared discrete policy. It does not establish empirical calibration, market optimality, profit maximization or financial suitability. The one-unit costs and the exact target-buffer equation are explicit author-model choices.

## Next seam

AMF-02 should freeze a calibration passport and adversarial scenario corpus before any operational recommendation is admitted.
