# CSS-03 / Полномочие не может заверить само себя

Дата: 04.08.2026  
Статус: формальный контракт и состязательные тесты протокола; физический помощник не установлен.

CSS-02 закрывает обычную гонку публичного имени: перед удалением точно открытый
объект переносится в эксклюзивный карантин. Осталась красная граница: враждебный
процесс с тем же пользователем обладает теми же файловыми полномочиями, что и
исполнитель.

CSS-03 фиксирует, почему ещё одна обёртка того же пользователя эту границу не
закроет:

```text
W(helper, quarantine) и не W(client, quarantine)  ->  client != helper
```

Клиент выбирает цель и фиксирует её личность, хеш политики, защищённое состояние,
эпоху и nonce. Отдельный помощник наблюдает и действует. Ответная квитанция
связывает результат с точным запросом. Root-личность и code identity нельзя
считать доказанными только потому, что они записаны внутри JSON; их обязан
сообщить доверенный канал операционной системы.

## Что проверено

- Lean 4: различие субъектов, сохранение защищённого состояния, точная привязка
  запроса и отклонение повторно появившегося публичного имени.
- Независимый от транспорта проверяющий протокола.
- Девять слепых сценариев: нормальный допуск, имитация root тем же UID,
  неподтверждённая code identity, изменение запроса, подмена объекта, изменение
  защищённого состояния, возврат имени, подмена политики и replay.
- Результат: 9/9 PASS.

## Опоры

- [Apple Service Management](https://developer.apple.com/documentation/servicemanagement/)
- [Apple: обновление helper executables](https://developer.apple.com/documentation/servicemanagement/updating-helper-executables-from-earlier-versions-of-macos)
- [Apple XPC updates](https://developer.apple.com/documentation/updates/xpc)
- [Apple TN3127](https://developer.apple.com/documentation/technotes/tn3127-inside-code-signing-requirements)
- [MITRE CWE-362](https://cwe.mitre.org/data/definitions/362.html)

## Красная граница

Подписанный `SMAppService` LaunchDaemon не установлен, физический XPC-пир не
аутентифицирован. Перед нами проверенный протокол следующей реализации, а не
заявление о уже достигнутой изоляции от того же UID. Рабочий статус остаётся CSS-02.

Канонические артефакты: [TMI Lean Formal Library](https://github.com/kernelpanic888/TMI-Lean-Formal-Library) · [живой ридер](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/certified-continuity-protocol/)
