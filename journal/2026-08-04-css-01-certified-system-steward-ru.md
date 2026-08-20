# CSS-01 · Сертифицированный системный распорядитель

**04.08.2026 · проверенный локальный срез · macOS refinement**

Формальная модель связана с функциональной системной программой так, чтобы shell-слой не мог самостоятельно придумывать политику.

## Контракт

```text
Lean-спецификация -> паспорт -> платформенный адаптер -> runtime-квитанция

AdmittedTransition =
  действие принадлежит полю
  и apply(before, action) = after
  и policy допускает(before, action, after)
  и protected(after) = protected(before)
```

Lean-аудит не обнаружил дополнительных аксиом у семи проверяемых теорем. Слепой runtime-пакет прошёл семь сценариев: штатная очистка, чужой путь, симлинк вместо цели, внутренний симлинк, изменение поля действий, изменение защищённого файла и противоречивые квитанции.

## macOS refinement

Исполнитель использует небольшой защищённый C-provider на файловых дескрипторах каталогов, `openat`, `fstatat` и `unlinkat`. Он не следует за симлинком внутри допущенного кэша, а политика, поле действий и защищённая проекция остаются в подписываемом паспорте.

Это закрывает обычный разрыв между проверкой и использованием, описанный в [MITRE CWE-367](https://cwe.mitre.org/data/definitions/367.html), и опирается на документированную в macOS семантику [`unlinkat`](https://manp.gs/mac/2/unlink), [`fstatat`](https://manp.gs/mac/2/stat) и [символических ссылок](https://manp.gs/mac/7/symlink).

## Красная граница

Это проверенный исследовательский срез, а не заявление о полном production-hardening. Финальная гонка имени ещё возможна, пока цель сначала не переносится в принадлежащий программе карантинный каталог или платформа не даёт эквивалентную возможность удалить уже проверенный объект.

## Канонические артефакты

- [Формальная модель](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/CertifiedSystemSteward.lean)
- [Исполнитель](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/certified-system-steward.mjs)
- [macOS-provider](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/platform/macos-safe-remove.c)
- [Adversarial review](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/CERTIFIED_SYSTEM_STEWARD_ADVERSARIAL_REVIEW.md)
- [Тесты](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/certified-system-steward.test.mjs)

