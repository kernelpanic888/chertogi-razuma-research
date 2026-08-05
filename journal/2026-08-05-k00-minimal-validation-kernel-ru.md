# AZ-00: исполнительный шлюз Agent Zero

`V_0, V_ext, Safe : X -> {0,1}`

`Exec_0(X)=some(X)` тогда и только тогда, когда `V_0(X)=1`, `V_ext(X)=1` и `Safe(X)=1`; иначе `none`.

Agent Zero действует только тогда, когда одно и то же действие прошло самовалидацию, внешнюю валидацию и контур безопасности. Полное совпадение возвращает исходное действие. Один ноль означает бездействие. Lean доказывает семантику связки, а исполнимый тест покрывает все восемь бинарных комбинаций.

[Lean-ядро](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AgentZeroValidationKernel.lean) · [таблица истинности](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/agent-zero-validation-kernel.test.mjs)
