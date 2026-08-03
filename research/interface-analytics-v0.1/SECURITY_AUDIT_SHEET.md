
## Security separation update - 2026-07-31

| ID | Проверка | Результат | Доказательство |
|---|---|---|---|
| SEC-28 | ResearchSecurity отделена от OperationalSecurity | PASS | Исследовательская модель сохранена как самостоятельная продуктовая ветка и не выдаётся за текущую runtime-защиту. |
| SEC-29 | Минимальная авторская поверхность P0 | PASS | SecretStore, IdentityStore, AdminCapability, Collector, D1, R2 и AuthorCookieAPI пусты. |
| SEC-30 | Чистая публичная версия v35 | PASS | Коммит a78ce13; 14/14 тестов безопасности; 22/22 публичного gate; live HTTP 200. |
| SEC-31 | H1 на границе провайдера | NOT CLAIMED | В живом ответе 0/5 экспериментальных заголовков; отрицательные v32-v34 сохранены как исследовательские следы. |
| SEC-32 | Статистика | DEFERRED P1 | Только будущие агрегаты без регистрации, raw IP/UA/referrer, visitor ID и авторских cookies; до отдельного слепого теста не развёртывается. |

Актуальный операционный паспорт: `OPERATIONAL_NON_POSSESSION_PASSPORT.md`. Исследовательский паспорт продукта: `SECURITY_RESEARCH_PRODUCT_PASSPORT.md`.

## P1 AggregateCounter candidate - 2026-07-31

| ID | Проверка | Результат | Доказательство |
|---|---|---|---|
| SEC-33 | Метаданные не влияют на sanitize/process | PASS | Две Lean-леммы без аксиом. |
| SEC-34 | Счётчик ограничен сверху | PASS | Две Lean-леммы, только `propext`; насыщение проверено Node-тестом. |
| SEC-35 | Белый список и нулевое тело | PASS | Инвариантные тесты `8/8`. |
| SEC-36 | Чёрноящичный поток | PASS | `768` случаев, `630` приняты, `35` дней, `0/10` запрещённых маркеров. |
| SEC-37 | Публичный runtime | NOT DEPLOYED | Кандидат находится только в `research/interface-analytics-v0.1`; P0 не менялся. |
| SEC-38 | Провайдер и сетевой адаптер | OPEN BOUNDARY | Требуется отдельная модель и живой тест до развёртывания. |

## P1 NetworkAdapter candidate - 2026-07-31

| ID | Проверка | Результат | Доказательство |
|---|---|---|---|
| SEC-39 | Запрещённые request capabilities | PASS | Proxy trap: `headers/cf/ip/UA/referrer/cookie/visitorId` не читаются. |
| SEC-40 | Минимальная HTTPS-проекция | PASS | Node `8/8`; exact origin/path, no body/query/credentials/fragment. |
| SEC-41 | Actor indistinguishability | PASS | Lean, без аксиом: одинаковый observable request даёт одинаковое решение. |
| SEC-42 | Глобальный предел работы | PASS | Node budget test; Lean upper-bound theorem, только `propext`. |
| SEC-43 | Human/bot classification | IMPOSSIBLE UNDER CONTRACT | Без идентификатора или внешней аттестации одинаковые запросы неразличимы. |
| SEC-44 | Публичный runtime | NOT DEPLOYED | Нет handler/storage binding; Sites v35 остаётся P0. |

## P1 AtomicStore candidate - 2026-07-31

| ID | Проверка | Результат | Доказательство |
|---|---|---|---|
| SEC-45 | Storage capability отсутствует | PASS | Lean: analytics=false, publicReader=true; без аксиом. |
| SEC-46 | Конкурентные инкременты | PASS | `128` попыток, итог `128`; потерянных обновлений нет. |
| SEC-47 | Бюджет под конкуренцией | PASS | Из `64` ровно `7` приняты и `57` отклонены при budget `7`. |
| SEC-48 | Rollback и восстановление очереди | PASS | Ошибка не меняет state; следующий переход проходит. |
| SEC-49 | Wire response и storage schema | PASS | Только empty status response; state содержит лишь day/kind/count. |
| SEC-50 | Persistent provider backend | OPEN BOUNDARY | Эталон in-memory не доказывает durability/replication/provider logs. |
