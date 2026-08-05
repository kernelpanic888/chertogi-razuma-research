# AISO-02: селектор не становится исполнителем

`Сертификат AISO -> AdmittedTransition CSS -> связанная квитанция -> проверка -> обучение`

Мост связывает паспорт, политику, наблюдение, поле действий, выбранное действие и оценку в один `selectionHash`. CSS независимо проверяет собственный контракт перехода и переносит этот хеш в намерение, квитанцию и свидетельство. Обучение возможно только по квитанции того же выбора после независимой проверки `HEAD`.

Корпус мутаций проверяет дрейф наблюдения и поля, подмену действия, изменение содержимого квитанции и неудачную проверку. Все эти случаи закрывают обучение. Пустое допустимое множество остаётся `NO_OP`.

Код: [формальный мост](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AISOToStewardBridge.lean) · [исполняемый мост](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/aiso-steward-bridge.mjs) · [adversarial-корпус](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/aiso-steward-bridge.test.mjs)

