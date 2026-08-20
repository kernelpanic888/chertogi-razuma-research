# CSS-02 · Карантинное уточнение

**04.08.2026 · проверенный локальный срез · 9/9 слепых сцен**

Certified System Steward больше не удаляет через публичное имя кэша. macOS-provider открывает допущенную сущность, эксклюзивно переносит её в закрытый quarantine с правами `0700` и удаляет относительно удерживаемых файловых дескрипторов.

```text
именованная цель = d -> эксклюзивный карантин(d) -> удалить(fd(d)) -> исходное имя отсутствует
```

Если исходное имя появляется снова, новая сущность сохраняется, а переход отклоняется. Это непосредственно сужает гонку между проверкой и использованием, описанную в [MITRE CWE-367](https://cwe.mitre.org/data/definitions/367.html); эксклюзивный перенос опирается на файловую возможность, документированную [Apple](https://developer.apple.com/documentation/foundation/urlresourcevalues/volumesupportsexclusiverenaming).

**Проверено:** runtime `9/9`; Lean-аудит по-прежнему подтверждает семь теорем без дополнительных аксиом; реальный preview ничего не удалил и не создал audit epoch.

**Красная граница:** враждебный параллельный процесс с тем же uid остаётся вне доказанной модели. Для production-статуса всё ещё нужны разделение привилегий или OS-возможность удаления по handle и независимая проверка.

[Карта ридера](../public/readers/certified-continuity-protocol/index.html#css02-steward) · [Provider](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/platform/macos-safe-remove.c) · [AR-02](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/CERTIFIED_SYSTEM_STEWARD_ADVERSARIAL_REVIEW.md) · [Тесты](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/certified-system-steward.test.mjs)

