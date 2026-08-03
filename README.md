# Chambers of the First Distinction

The canonical source of the public research site:

https://chertogi-razuma-research.kernelpanic888.chatgpt.site/

This repository is the source of truth. Production deployments are built from a named Git commit; the hosting repository is only a deployment mirror.

## Research architecture

- one continuous bilingual public map;
- self-contained HTML readers under `public/readers/`;
- inline CSS and JavaScript only inside public readers;
- no external runtime dependencies for reader content;
- a minimal D1 binding used only by the anonymous page-view counter;
- no R2 storage, public forms, cookies, service workers or hidden admin route.

Cryptographic reference code is intentionally maintained in a separate repository and linked from the self-contained CR-01 reader:

https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol

The CR-03 branch adds an executable physical-anchor provider contract, a development-only simulator, a Lean relation for anchored successors and a bilingual visual research map. It remains a laboratory candidate until a real hardware provider and frozen attack matrix are independently exercised.

## Research journal

The bilingual **Journal of the First Distinction / Журнал первого различия** records research transitions without duplicating the canonical code:

https://github.com/kernelpanic888/chertogi-razuma-research/tree/main/journal

## Build and boundary check

```bash
npm ci
npm run build
npm run test:security
```

## Status boundary

The site distinguishes definitions, formal theorems, model bridges, empirical results and open hypotheses. A Lean proof checks a consequence of stated assumptions; it does not by itself prove that the formal objects describe physical reality.

Author: Salkutsan Aleksey Anatolievich  
ORCID: https://orcid.org/0009-0006-8717-0492
