# Паспорт IF-BS-22F-F8C29

## Имя

Raw finite sample certification / Сертификация сырой конечной выборки.

## Вход

- Exact forward and inverse squared extrema F8C17/F8C27.
- Exact directional diamond and finite delta-coverage machinery.
- Forward and reciprocal regularity moduli.
- Certified noisy identifiability interval F8C28.

## Новые доказанные узлы

- Разделение приборного шума eta и вычислительного разрешения rho.
- Нижний corrected sample maximum S_minus.
- Верхний mesh-corrected maximum S_plus.
- Полный квадратный интервал S_minus<=S_exact<=S_plus.
- Корневой transport O=sqrt(S_plus), epsilon=sqrt(S_plus)-sqrt(S_minus).
- Полный inverse regularity bound для 0<=a<1 без старого ограничения sqrt(2)a<1.
- Автоматическое построение CertifiedNoisyMetricReading из двух raw finite samples.

## Статус утверждения

Красная граница F8C28 закрыта на уровне доказательного сертификата: raw sample, mesh и bounded noise порождают eps_F и eps_B. Предпосылки coverage и interval validity ещё должны быть вычислены явным checker.

## Проверяемый носитель

- `formal/IntrinsicNonradialShearRawSampleCertification.lean`
- `formal/IntrinsicNonradialShearRawSampleCertificationAudit.lean`

## Красная граница

Нужен исполнимый рациональный mesh-checker с interval arithmetic и сериализуемым certificate record.

## Следующий шаг

IF-BS-22F-F8C30: executable rational delta-net certificate.
