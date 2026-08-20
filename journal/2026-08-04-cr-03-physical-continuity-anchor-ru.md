# CR-03 · Физический якорь непрерывности

**Дата:** 2026-08-04  
**Статус:** исполняемый контракт провайдера и рабочая физическая модель  
**Автор:** Салкуцан Алексей Анатольевич

## Чтение

Следующий слой защиты не является блокчейном или новым шифром. Он связывает принятую вершину непрерывности с физическим якорем, который должен защищать ключ подписи, монотонную эпоху и измеренное окружение.

`P_n = (anchorId, id, n, parentHead, stateHead, H(measurements), H(challenge))`

`R_n = (P_n, measurements, Sign(sk_anchor, domain || canonical(P_n)))`

Исполняемый контракт принимает только точную следующую эпоху, закреплённую идентичность и ожидаемые родительскую и новую вершины. Свежий challenge не позволяет старой квитанции отвечать в новой сессии. Независимые свидетели сравнивают квитанции, а не приватное состояние.

Две корректные квитанции одного закреплённого якоря с одной идентичностью, эпохой и родителем, но разными вершинами являются свидетельством двоения или клонирования якоря при принятых предпосылках. Они не выбирают истинную ветвь.

## Канонические артефакты

- [Живая физическая карта CR-03](https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/certified-continuity-protocol/#cr03-physical-anchor)
- [Эталонный код провайдера](https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol/blob/4498e361929ecf78342303877469caa2e82153f2/src/physical-anchor.mjs)
- [Паспорт физического якоря](https://github.com/kernelpanic888/Salkutsan-Certified-Continuity-Protocol/blob/4498e361929ecf78342303877469caa2e82153f2/docs/PHYSICAL_ANCHOR.md)
- [IETF RATS Architecture, RFC 9334](https://www.rfc-editor.org/rfc/rfc9334.html)
- [Remote Integrity Verification with TPMs, RFC 9683](https://www.rfc-editor.org/rfc/rfc9683.html)
- [Спецификации TPM от Trusted Computing Group](https://trustedcomputinggroup.org/work-groups/trusted-platform-module/)

## Граница

Lean фиксирует следствие отношения anchored successor. Это не доказывает физическую честность конкретного TPM, счётчика, корня измерений или provisioning. Встроенный провайдер является программным симулятором.

## Следующий шаг по паспорту

Реализовать настоящий провайдер класса TPM и выполнить матрицу атак: rollback, replay, изменение измеренного состояния, разделение и соединение свидетелей.
